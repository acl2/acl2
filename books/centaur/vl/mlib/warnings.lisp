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
(include-book "fmt")
(local (include-book "finite-set-theory/osets/set-order" :dir :system))
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(defsection downcase

;; BOZO optimize and move to string library

  (defund downcase-chars (x)
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        nil
      (let ((code (char-code (car x))))
        (cons (if (and (<= (char-code #\A) code)
                       (<= code (char-code #\Z)))
                  (code-char
                   (+ (char-code #\a)
                      (- code (char-code #\A))))
                (car x))
              (downcase-chars (cdr x))))))

  (defthm character-listp-of-downcase-chars
    (implies (force (character-listp x))
             (character-listp (downcase-chars x)))
    :hints(("Goal" :in-theory (enable downcase-chars))))

  (defund downcase (x)
    (declare (type string x))
    (coerce (downcase-chars (coerce x 'list)) 'string))

  (defthm stringp-of-downcase
    (stringp (downcase x))))




(defsection vl-modulelist-clean-warnings
  :parents (warnings)
  :short "Clean the warnings of every module in a module list."
  :long "<p><b>Signature:</b> @(call vl-modulelist-clean-warnings) returns
<tt>X-PRIME</tt>.</p>

<p>We change every module in <tt>X</tt> by applying @(see vl-clean-warnings) to
its warnings, and return the updated list of modules.  It may occasionally be
useful to run this transformation to clean up any redundant warnings that have
crept into the module list.</p>"

  (defund vl-modulelist-clean-warnings (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (if (atom x)
        nil
      (let* ((old-warnings (vl-module->warnings (car x)))
             (new-warnings (vl-clean-warnings old-warnings)))
        (cons (change-vl-module (car x) :warnings new-warnings)
              (vl-modulelist-clean-warnings (cdr x))))))

  (local (in-theory (enable vl-modulelist-clean-warnings)))

  (defthm vl-modulelist-p-of-vl-modulelist-clean-warnings
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-clean-warnings x))))

  (defthm vl-modulelist->names-of-vl-modulelist-clean-warnings
    (equal (vl-modulelist->names (vl-modulelist-clean-warnings x))
           (vl-modulelist->names x))))



(defsection vl-modulelist-flat-warnings
  :parents (warnings)
  :short "Gather all warnings from a @(see vl-modulelist-p) into a single @(see
vl-warninglist-p)."
  :long "<p>This function appends together the warnings from all modules in a
module list.</p>

<p><b>Note</b>: if you want to summarize or print warnings, a @(see
vl-modwarningalist-p) is typically more useful than a flat list of
warnings.</p>

<p><b>Note</b>: this function does not clean the warnings in any way, and so
you may end up with many redundant warnings.  Because of this, it is probably a
good idea to call @(see vl-modulelist-clean-warnings) first, which cleans the
warnings of each module individually, before appending them all together.</p>"

  (defmapappend vl-modulelist-flat-warnings (x)
    (vl-module->warnings x)
    :guard (vl-modulelist-p x)
    :transform-true-list-p nil)

  (local (in-theory (enable vl-modulelist-flat-warnings)))

  (defthm vl-warninglist-p-of-vl-modulelist-flat-warnings
    (implies (force (vl-modulelist-p x))
             (vl-warninglist-p (vl-modulelist-flat-warnings x)))))



(defsection vl-modwarningalist-p
  :parents (warnings)
  :short "A (fast) alist associating names to warnings."

  :long "<p>A modwarningalist associates strings to lists of warnings, and are
typically fast alists.</p>

<p>There are two common uses for modwarningalists.</p>

<p>First, we may generate such an alist when we want to associate some warnings
with a variety of modules.  That is, imagine a transformation that wants to add
warnings to five distinct modules.  It would be somewhat awkward to iteratively
update the @(see vl-modulelist-p), so instead we might create a modwarningalist
that associates target module names with the new warnings we want to add to
them.  The function @(see vl-apply-modwarningalist) can then be used to add
these warnings to a module list.</p>

<p>Second, modwarningalists can be useful when we want to print the warnings
for a bunch of modules.  Depending on the context, we might want to associate
either the orignames or names of the modules to their related warnings.</p>"

;; BOZO switch to defalist?

  (defund vl-modwarningalist-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        t
      (and (consp (car x))
           (stringp (caar x))
           (vl-warninglist-p (cdar x))
           (vl-modwarningalist-p (cdr x)))))

  (local (in-theory (enable vl-modwarningalist-p)))

  (defthm vl-modwarningalist-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-modwarningalist-p x)
                    t)))

  (defthm vl-modwarningalist-p-of-cons
    (equal (vl-modwarningalist-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (vl-warninglist-p (cdr a))
                (vl-modwarningalist-p x))))

  (defthm vl-warninglist-p-of-cdr-of-hons-assoc-equal-when-vl-modwarningalist-p
    (implies (vl-modwarningalist-p x)
             (vl-warninglist-p (cdr (hons-assoc-equal a x)))))

  (defthm vl-modwarningalist-p-of-append
    (implies (and (vl-modwarningalist-p x)
                  (vl-modwarningalist-p y))
             (vl-modwarningalist-p (append x y))))

  (defthm vl-modwarningalist-p-of-hons-shrink-alist
    (implies (and (vl-modwarningalist-p x)
                  (vl-modwarningalist-p acc))
             (vl-modwarningalist-p (hons-shrink-alist x acc)))
    :hints(("Goal" :in-theory (enable (:induction hons-shrink-alist)))))

  (defthm vl-modwarningalist-p-of-insert
    (implies (and (consp a)
                  (stringp (car a))
                  (vl-warninglist-p (cdr a))
                  (vl-modwarningalist-p x))
             (vl-modwarningalist-p (insert a x)))
    :hints(("Goal" :in-theory (enable sets::primitive-reasoning insert))))

  (defthm vl-modwarningalist-p-of-mergesort
    (implies (force (vl-modwarningalist-p x))
             (vl-modwarningalist-p (mergesort x))))

  (defthm string-listp-of-alist-keys-when-vl-modwarningalist-p
    (implies (vl-modwarningalist-p x)
             (string-listp (alist-keys x)))
    :hints(("Goal" :induct (len x)))))




(defsection vl-extend-modwarningalist
  :parents (warnings)
  :short "Add a single warning to a @(see vl-modwarningalist-p)."

  :long "<p><b>Signature:</b> @(call vl-extend-modwarningalist) produces a new
warning alist.</p>

<p>This function is useful in the incremental construction of warning alists;
it adds a particular <tt>warning</tt> to the existing warnings for
<tt>modname</tt> in <tt>walist</tt>.</p>"

  (defund vl-extend-modwarningalist (modname warning walist)
    (declare (xargs :guard (and (stringp modname)
                                (vl-warning-p warning)
                                (vl-modwarningalist-p walist))))
    (let* ((old-warnings (cdr (hons-get modname walist)))
           (new-warnings (cons warning old-warnings)))
      (hons-acons modname new-warnings walist)))

  (local (in-theory (enable vl-extend-modwarningalist)))

  (defthm vl-modwarningalist-p-of-vl-extend-modwarningalist
    (implies (and (force (stringp modname))
                  (force (vl-warning-p warning))
                  (force (vl-modwarningalist-p walist)))
             (vl-modwarningalist-p (vl-extend-modwarningalist modname warning walist)))))



(defsection vl-extend-modwarningalist-list
  :parents (warnings)
  :short "Add a list of warnings to a @(see vl-modwarningalist-p)."

  :long "<p><b>Signature:</b> @(call vl-extend-modwarningalist-list) produces a new
warning alist.</p>

<p>This function is useful in the incremental construction of warning alists;
it adds the list of <tt>warnings</tt> to the existing warnings for
<tt>modname</tt> in <tt>walist</tt>.</p>"

  (defund vl-extend-modwarningalist-list (modname warnings walist)
    (declare (xargs :guard (and (stringp modname)
                                (vl-warninglist-p warnings)
                                (vl-modwarningalist-p walist))))
    (let* ((old-warnings (cdr (hons-get modname walist)))
           (new-warnings (append-without-guard warnings old-warnings)))
      (hons-acons modname new-warnings walist)))

  (local (in-theory (enable vl-extend-modwarningalist-list)))

  (defthm vl-modwarningalist-p-of-vl-extend-modwarningalist-list
    (implies (and (force (stringp modname))
                  (force (vl-warninglist-p warnings))
                  (force (vl-modwarningalist-p walist)))
             (vl-modwarningalist-p (vl-extend-modwarningalist-list modname warnings walist)))))



(defsection vl-apply-modwarningalist
  :parents (warnings)
  :short "Annotate modules with the warnings named in a @(see
vl-modwarningalist-p)."

  :long "<p><b>Signature:</b> @(call vl-apply-modwarningalist) returns
<tt>mods-prime</tt>.</p>

<p>We are given <tt>x</tt>, a @(see vl-modulelist-p), and <tt>alist</tt>, a
@(see vl-modwarningalist-p), which should be a fast alist.  We change
<tt>x</tt> by adding any warnings that are associated with each module's name
in <tt>alist</tt>.</p>"

  (defund vl-apply-modwarningalist-aux (x alist)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modwarningalist-p alist))))
    (let ((entry (hons-get (vl-module->name x) alist)))
      (if (not entry)
          x
        (let* ((warnings (vl-module->warnings x))
               (warnings (revappend-without-guard (cdr entry) warnings)))
          (change-vl-module x :warnings warnings)))))

  (defthm vl-module-p-of-vl-apply-modwarningalist-aux
    (implies (and (force (vl-module-p x))
                  (force (vl-modwarningalist-p alist)))
             (vl-module-p (vl-apply-modwarningalist-aux x alist)))
    :hints(("Goal" :in-theory (enable vl-apply-modwarningalist-aux))))

  (defthm vl-module->name-of-vl-apply-modwarningalist-aux
    (equal (vl-module->name (vl-apply-modwarningalist-aux x alist))
           (vl-module->name x))
    :hints(("Goal" :in-theory (enable vl-apply-modwarningalist-aux))))


  (defprojection vl-apply-modwarningalist (x alist)
    (vl-apply-modwarningalist-aux x alist)
    :guard (and (vl-modulelist-p x)
                (vl-modwarningalist-p alist))
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-apply-modwarningalist)))

  (defthm vl-modulelist->names-of-vl-apply-modwarningalist
    (equal (vl-modulelist->names (vl-apply-modwarningalist x alist))
           (vl-modulelist->names x))))


(defsection vl-clean-modwarningalist
  :parents (warnings)
  :short "@(call vl-clean-modwarningalist) shrinks a @(see
vl-modwarningalist-p) and cleans all of its warning lists with @(see
vl-clean-warnings)."

  :long "<p>We return a new fast-alist that is independent of <tt>x</tt>.  Any
modules which have no warnings are eliminated.</p>"

  (defund vl-clean-modwarningalist-aux (x acc)
    "Assumes X has already been shrunk, so we may safely recur down it."
    (declare (xargs :guard (and (vl-modwarningalist-p x)
                                (vl-modwarningalist-p acc))))
    (if (atom x)
        acc
      (let* ((name     (caar x))
             (warnings (vl-clean-warnings (cdar x)))
             (acc      (if (atom warnings)
                           acc
                         (hons-acons name warnings acc))))
        (vl-clean-modwarningalist-aux (cdr x) acc))))

  (defund vl-clean-modwarningalist (x)
    (declare (xargs :guard (vl-modwarningalist-p x)))
    (b* ((x-shrink (hons-shrink-alist x nil))
         (ret      (vl-clean-modwarningalist-aux x-shrink nil))
         (-        (fast-alist-free x-shrink)))
        ret))

  (local (in-theory (enable vl-clean-modwarningalist
                            vl-clean-modwarningalist-aux)))

  (defthm vl-modwarningalist-p-of-vl-clean-modwarningalist-aux
    (implies (and (vl-modwarningalist-p x)
                  (vl-modwarningalist-p acc))
             (vl-modwarningalist-p (vl-clean-modwarningalist-aux x acc))))

  (defthm vl-modwarningalist-p-of-vl-clean-modwarningalist
    (implies (force (vl-modwarningalist-p x))
             (vl-modwarningalist-p (vl-clean-modwarningalist x)))))




(defsection vl-origname-modwarningalist
  :parents (warnings)
  :short "@(call vl-origname-modwarningalist) constructs a @(see
vl-modwarningalist-p) from a module list, using <tt>orignames</tt> as the
keys."

  :long "<p>Unparameterization causes problems for printing warnings about each
module, because, e.g., instead of having warnings about <tt>adder</tt>, we
actually have warnings about <tt>adder$width=5</tt> and
<tt>adder$width=13</tt>, etc.  Yet the end-user typically shouldn't be bothered
with looking at the warnings for each specialized version of <tt>adder</tt>; he
just wants to see all of the warnings.</p>

<p>This function gathers up all warnings associated with each module, and
builds a @(see vl-modwarningalist-p) that maps <tt>orignames</tt> to warnings.
We take care to ensure that all of the warnings associated with each name are
properly cleaned up and merged.</p>"

  (defund vl-origname-modwarningalist-aux (x acc)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (vl-modwarningalist-p acc))))
    (if (atom x)
        acc
      (let* ((origname      (vl-module->origname (car x)))
             (my-warnings   (vl-module->warnings (car x)))
             (prev-warnings (cdr (hons-get origname acc)))
             (new-warnings  (revappend-without-guard my-warnings prev-warnings))
             (acc           (hons-acons origname new-warnings acc)))
        (vl-origname-modwarningalist-aux (cdr x) acc))))

  (defund vl-origname-modwarningalist (x)
    (declare (xargs :guard (vl-modulelist-p x)
                    :verify-guards nil))
    (b* ((unclean (vl-origname-modwarningalist-aux x nil))
         (ret     (vl-clean-modwarningalist unclean))
         (-       (fast-alist-free unclean)))
        ret))

  (local (in-theory (enable vl-origname-modwarningalist-aux
                            vl-origname-modwarningalist)))

  (defthm vl-modwarningalist-p-of-vl-origname-modwarningalist-aux
    (implies (and (force (vl-modulelist-p x))
                  (force (vl-modwarningalist-p acc)))
             (vl-modwarningalist-p (vl-origname-modwarningalist-aux x acc))))

  (verify-guards vl-origname-modwarningalist)

  (defthm vl-modwarningalist-p-of-vl-origname-modwarningalist
    (implies (force (vl-modulelist-p x))
             (vl-modwarningalist-p (vl-origname-modwarningalist x)))))



(defpp vl-print-warning (x)
  :parents (warnings)
  :short "Pretty-print a @(see vl-warning-p)."
  :guard (vl-warning-p x)
  :body
  (let ((type   (vl-warning->type x))
        (msg    (vl-warning->msg x))
        (args   (vl-warning->args x))
        (fatalp (vl-warning->fatalp x))
        (fn     (vl-warning->fn x))
        (htmlp  (vl-ps->htmlp)))
    (if (not htmlp)
        (b* ((note   (cond ((and fn fatalp)
                            (str::cat " (fatal, from " (downcase (symbol-name fn)) ")"))
                           (fatalp
                            " (fatal)")
                           (fn
                            (str::cat " (from " (downcase (symbol-name fn)) ")"))
                           (t
                            "")))
             (ps     (vl-ps-seq
                      (vl-print (symbol-name type))
                      (vl-println note)
                      (vl-indent (vl-ps->autowrap-ind))))
             ;; Some warnings produced by DEFM can be absurdly long, so, for
             ;; now, we limit warnings to 3K characters.
             (limit  (if (eq type :defm-fail)
                         3000
                       nil))
             (config (vl-ps-save-config))
             (col    (vl-ps->col))
             (ext    (with-local-ps (vl-ps-load-config config)
                                    (vl-ps-update-col col)
                                    (vl-cw-obj msg args)))
             (len    (length ext))

             (rchars (vl-ps->rchars))
             (rchars
              (b* (((when (or (not limit) (< len limit)))
                    (cons #\Newline (str::revappend-chars ext rchars)))
                   ;; Else, chop down the message.
                   (chop (subseq ext 0 limit))
                   (rchars (str::revappend-chars chop rchars))
                   (rchars (str::revappend-chars "[... " rchars))
                   (rchars (str::revappend-chars (str::natstr (- len limit)) rchars))
                   (rchars (str::revappend-chars " more characters ...]" rchars))
                   (rchars (cons #\Newline rchars)))
                rchars)))
          (vl-ps-seq
           (vl-ps-update-rchars rchars)
           (vl-ps-update-col 0)))
      ;; HTML mode
      (vl-ps-seq
       (vl-print-markup "<li class=\"vl_warning\">")
       (if fatalp
           (vl-print-markup "<span class=\"vl_fatal_warning\" title=\"From ")
         (vl-print-markup "<span class=\"vl_warning_type\" title=\"From "))
       (if fn
           (vl-print-markup (symbol-name fn))
         (vl-print-markup "[not available]"))
       (vl-print-markup "\">")
       (vl-print (symbol-name type))
       (vl-print-markup "</span>")
       ;; We don't constrain the message size because it's hard to deal with
       ;; tag closing in html mode.
       (vl-print-markup " ")
       (vl-cw-obj msg args)
       (vl-println-markup "</li>")))))

(defpp vl-print-warnings-aux (x)
  :guard (vl-warninglist-p x)
  :body (if (atom x)
            ps
          (vl-ps-seq
           (if (vl-ps->htmlp)
               ps
             (vl-ps-seq
              (vl-println "")
              (vl-indent 2)))
           (vl-print-warning (car x))
           (vl-print-warnings-aux (cdr x)))))

(defpp vl-print-warnings (x)
  :parents (warnings)
  :short "Pretty-print a @(see vl-warninglist-p)."
  :long "<p>We automatically clean the warnings; see @(see vl-clean-warnings).</p>

<p>Note that no header information is printed, this just prints the list of
warnings.</p>

<p>See also @(see vl-print-warnings-with-header) and @(see
vl-warnings-to-string).</p>"

  :guard (vl-warninglist-p x)
  :body (let* ((htmlp (vl-ps->htmlp))
               (x (vl-clean-warnings x)))
          (cond ((not htmlp)
                 (vl-print-warnings-aux x))
                ((atom x)
                 ps)
                (t
                 (vl-ps-seq
                  (vl-println-markup "<ul class=\"vl_warning_list\">")
                  (vl-print-warnings-aux x)
                  (vl-println-markup "</ul>"))))))

(defpp vl-print-warnings-with-header (x)
  :parents (warnings)
  :short "Pretty-print a @(see vl-warninglist-p) with a header saying how many
warnings there are."
  :long "<p>This is almost identical to @(see vl-print-warnings), but it also
prefaces the list of warnings with a header that says how many warnings there
are.  Also, whereas @(see vl-print-warnings) is essentially invisible if there
are no warnings, in such cases this function at least prints \"No
warnings\".</p>"
  :guard (vl-warninglist-p x)
  :body (b* ((htmlp (vl-ps->htmlp))
             (x    (vl-clean-warnings x))
             (msg  (cond ((atom x) "No Warnings")
                         ((atom (cdr x)) "One Warning")
                         (t (str::cat (str::natstr (len x)) " Warnings")))))

            (if (not htmlp)
                (vl-ps-seq (vl-println msg)
                           (vl-print-warnings-aux x))

              (vl-ps-seq
               (vl-println-markup "<div class=\"vl_module_warnings\">")
               (if (atom x)
                   (vl-print-markup "<h3 class=\"vl_module_no_warnings\">")
                 (vl-print-markup "<h3 class=\"vl_module_yes_warnings\">"))
               (vl-print msg)
               (vl-println-markup "</h3>")

               (if (atom x)
                   ps
                 (vl-ps-seq
                  (vl-println-markup "<ul class=\"vl_warning_list\">")
                  (vl-print-warnings-aux x)
                  (vl-println-markup "</ul>")))

               (vl-println-markup "</div>")))))


(defsection vl-warnings-to-string
  :parents (warnings)
  :short "Pretty-print a @(see vl-warninglist-p) into a string."
  :long "<p>See @(see vl-print-warnings-with-header) and @(see with-local-ps).</p>"

  (defund vl-warnings-to-string (warnings)
    (declare (xargs :guard (vl-warninglist-p warnings)))
    (with-local-ps (vl-print-warnings-with-header warnings)))

  (defthm stringp-of-vl-warnings-to-string
    (stringp (vl-warnings-to-string warnings))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable vl-warnings-to-string)))))



(defpp vl-print-warnings-with-named-header (modname x)
  :parents (warnings)
  :guard (and (stringp modname)
              (vl-warninglist-p x))
  :body (b* ((htmlp (vl-ps->htmlp))
             (x    (vl-clean-warnings x))
             (msg  (cond ((atom x) "No Warnings")
                         ((atom (cdr x)) "One Warning")
                         (t (str::cat (str::natstr (len x)) " Warnings")))))
            (if (not htmlp)
                (if (atom x)
                    ps
                  (vl-ps-seq (vl-println "")
                             (vl-print modname)
                             (vl-print " -- ")
                             (vl-println msg)
                             (vl-print-warnings-aux x)))

              (vl-ps-seq
               (vl-println-markup "<div class=\"vl_module_warnings\">")
               (if (atom x)
                   (vl-print-markup "<h3 class=\"vl_module_no_warnings\">")
                 (vl-print-markup "<h3 class=\"vl_module_yes_warnings\">"))
               (vl-print-modname modname)
               (vl-print ": ")
               (vl-print msg)
               (vl-println-markup "</h3>")

               (if (atom x)
                   ps
                 (vl-ps-seq
                  (vl-println-markup "<ul class=\"vl_warning_list\">")
                  (vl-print-warnings-aux x)
                  (vl-println-markup "</ul>")))

               (vl-println-markup "</div>")))))

(defpp vl-print-modwarningalist-aux (x)
  :parents (warnings)
  :guard (vl-modwarningalist-p x)
  :body
  (if (atom x)
      ps
    (vl-ps-seq
     (vl-print-warnings-with-named-header (caar x) (cdar x))
     (vl-println "")
     (vl-print-modwarningalist-aux (cdr x)))))

(defpp vl-print-modwarningalist (x)
  :parents (warnings)
  :short "Pretty-print a @(see vl-modwarningalist-p)."
  :long "<p>See also @(see vl-modwarningalist-to-string).</p>"
  :guard (vl-modwarningalist-p x)
  :body
  (b* ((x-shrink (hons-shrink-alist x nil))
       (-        (fast-alist-free x-shrink))
       (x-sorted (mergesort x-shrink)))
      (vl-print-modwarningalist-aux x-sorted)))

(defsection vl-modwarningalist-to-string
  :parents (warnings)
  :short "Pretty-print a @(see vl-modwarningalist-p) into a string."
  :long "<p>See also @(see vl-print-modwarningalist).</p>"

  (defund vl-modwarningalist-to-string (x)
    (declare (xargs :guard (vl-modwarningalist-p x)))
    (with-local-ps (vl-print-modwarningalist x)))

  (local (in-theory (enable vl-modwarningalist-to-string)))

  (defthm stringp-of-vl-modwarningalist-to-string
    (stringp (vl-modwarningalist-to-string x))
    :rule-classes :type-prescription))

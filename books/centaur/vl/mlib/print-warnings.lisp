; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "reportcard")
(include-book "fmt")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(define vl-print-warning-text-mode ((x vl-warning-p) &key (ps 'ps))
  :parents (vl-print-warning)
  (b* (((vl-warning x) x)
       (note
        (cond ((and x.fn x.fatalp)
               (cat " (fatal, from " (str::downcase-string (symbol-name x.fn)) ")"))
              (x.fatalp
               " (fatal)")
              (x.fn
               (cat " (from " (str::downcase-string (symbol-name x.fn)) ")"))
              (t
               ""))))
    (vl-ps-seq (vl-print (symbol-name x.type))
               (vl-println note)
               (vl-indent (vl-ps->autowrap-ind))
               (if x.context
                   (vl-cw-obj "~a0: ~@1" (list x.context (vl-msg x.msg x.args)))
                 (vl-cw-obj x.msg x.args))
               (vl-println ""))))

(define vl-print-warning-html-mode ((x vl-warning-p) &key (ps 'ps))
  (b* (((vl-warning x) x))
    (vl-ps-seq
     (vl-print-markup "<li class=\"vl_warning\">")
     (if x.fatalp
         (vl-print-markup "<span class=\"vl_fatal_warning\" title=\"From ")
       (vl-print-markup "<span class=\"vl_warning_type\" title=\"From "))
     (if x.fn
         (vl-print-markup (symbol-name x.fn))
       (vl-print-markup "[not available]"))
     (vl-print-markup "\">")
     (vl-print (symbol-name x.type))
     (vl-print-markup "</span>")
     ;; We don't constrain the message size because it's hard to deal with
     ;; tag closing in html mode.
     (vl-print-markup " ")
     (if x.context
         (vl-cw-obj "~a0: ~@1" (list x.context (vl-msg x.msg x.args)))
       (vl-cw-obj x.msg x.args))
     (vl-println-markup "</li>"))))

(define vl-print-warning ((x vl-warning-p) &key (ps 'ps))
  :parents (warnings)
  :short "Pretty-print a @(see vl-warning)."
  (if (vl-ps->htmlp)
      (vl-print-warning-html-mode x)
    (vl-print-warning-text-mode x)))

(define vl-print-warnings-aux ((x vl-warninglist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (if (vl-ps->htmlp)
                   ps
                 (vl-ps-seq (vl-println "")
                            (vl-indent 2)))
               (vl-print-warning (car x))
               (vl-print-warnings-aux (cdr x)))))

(define vl-print-warnings ((x vl-warninglist-p) &key (ps 'ps))
  :parents (vl-warninglist)
  :short "Pretty-print a @(see vl-warninglist)."
  :long "<p>We automatically clean the warnings; see @(see vl-clean-warnings).</p>

<p>Note that no header information is printed, this just prints the list of
warnings.</p>

<p>See also @(see vl-print-warnings-with-header) and @(see
vl-warnings-to-string).</p>"

  (let* ((htmlp (vl-ps->htmlp))
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

(define vl-print-warnings-with-header ((x vl-warninglist-p) &key (ps 'ps))
  :parents (vl-warninglist)
  :short "Pretty-print a @(see vl-warninglist) with a header saying how many
warnings there are."
  :long "<p>This is almost identical to @(see vl-print-warnings), but it also
prefaces the list of warnings with a header that says how many warnings there
are.  Also, whereas @(see vl-print-warnings) is essentially invisible if there
are no warnings, in such cases this function at least prints \"No
warnings\".</p>"
  (b* ((htmlp (vl-ps->htmlp))
       (x    (vl-clean-warnings x))
       (msg  (cond ((atom x) "No Warnings")
                   ((atom (cdr x)) "One Warning")
                   (t (cat (natstr (len x)) " Warnings")))))

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

(define vl-warnings-to-string ((warnings vl-warninglist-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (vl-warninglist)
  :short "Pretty-print a @(see vl-warninglist) into a string."
  :long "<p>See @(see vl-print-warnings-with-header) and @(see with-local-ps).</p>"
  (with-local-ps (vl-print-warnings-with-header warnings)))

(define vl-print-warnings-with-named-header ((modname stringp)
                                             (x vl-warninglist-p)
                                             &key (ps 'ps))
  :parents (vl-warninglist)
  (b* ((htmlp (vl-ps->htmlp))
       (x    (vl-clean-warnings x))
       (msg  (cond ((atom x) "No Warnings")
                   ((atom (cdr x)) "One Warning")
                   (t (cat (natstr (len x)) " Warnings")))))
    (if (not htmlp)
        (if (atom x)
            ps
          (vl-ps-seq (vl-println "")
                     (vl-print-str modname)
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



(define vl-elide-warnings-main
  :parents (vl-elide-warnings)
  ((x          vl-warninglist-p)
   (cutoff     natp "Max number of warnings of a single type to keep.")
   (suppressed symbol-listp
               "Types of warnings, with duplicates, that we have suppressed
                so far.")
   (counts-fal "Fast alist, binds @('type -> count'), where count is how many
                warnings of this type have been seen so far.")
   (acc        vl-warninglist-p))
  :returns (mv (acc        vl-warninglist-p)
               (counts-fal )
               (suppressed symbol-listp))
  :measure (len x)
  :guard-debug t
  (b* ((x          (vl-warninglist-fix x))
       (acc        (vl-warninglist-fix acc))
       (cutoff     (lnfix cutoff))

       ((when (atom x))
        (mv acc cutoff (acl2::symbol-list-fix suppressed)))

       ((vl-warning x1) (car x))
       (curr            (nfix (cdr (hons-get x1.type counts-fal))))
       (counts-fal      (hons-acons x1.type (+ 1 curr) counts-fal))
       (keep-p          (< curr cutoff))
       (acc             (if keep-p (cons x1 acc) acc))
       (suppressed      (if keep-p suppressed (cons x1.type (acl2::symbol-list-fix suppressed)))))
    (vl-elide-warnings-main (cdr x) cutoff suppressed counts-fal acc)))

(define vl-elide-warnings
  :parents (vl-print-reportcard)
  :short "Cut down excessive warnings of certain types."
  ((warnings vl-warninglist-p "Warnings to filter.")
   (cutoff   maybe-natp       "Max warnings of each type to permit, or NIL for no eliding."))
  :returns (new-warnings vl-warninglist-p)
  (b* (((unless cutoff)
        (vl-warninglist-fix warnings))
       ((mv warnings counts-fal suppressed)
        (vl-elide-warnings-main warnings cutoff nil nil nil))
       (- (fast-alist-free counts-fal))
       ((unless (consp suppressed))
        ;; No changes, nothing to warn about.
        warnings))
    (warn :type :vl-elided-warnings
          :msg "Eliding ~x0 additional warning~s1 (type~s1 ~&2)."
          :args (list (len suppressed)
                      (if (vl-plural-p suppressed) "s" "")
                      (mergesort suppressed)))))

(define vl-print-reportcard-aux ((x vl-reportcard-p)
                                 (elide maybe-natp)
                                 &key (ps 'ps))
  :parents (vl-print-reportcard)
  :measure (vl-reportcard-count x)
  :verbosep t
  (b* ((x     (vl-reportcard-fix x))
       (elide (maybe-natp-fix elide))
       ((when (atom x))
        ps)
       ((cons name warnings) (car x))
       ((unless warnings)
        (vl-print-reportcard-aux (cdr x) elide)))
    (vl-ps-seq (vl-print-warnings-with-named-header
                (if (equal name :design) "Design Root" name)
                (vl-elide-warnings warnings elide))
               (vl-println "")
               (vl-print-reportcard-aux (cdr x) elide)))
  :prepwork
  ((local (defthm l0
            (implies (and (vl-reportcardkey-p x)
                          (not (equal x :design)))
                     (stringp x))
            :hints(("Goal" :in-theory (enable vl-reportcardkey-p)))))))

(define vl-print-reportcard ((x vl-reportcard-p)
                             &key
                             ((elide maybe-natp) '3)
                             (ps 'ps))
  :parents (vl-reportcard)
  :short "Pretty-print a @(see vl-reportcard-p)."
  :long "<p>See also @(see vl-reportcard-to-string).</p>"
  (b* ((x        (vl-reportcard-fix x))
       (x-shrink (hons-shrink-alist x nil))
       (-        (fast-alist-free x-shrink))
       (x-sorted (mergesort x-shrink)))
      (vl-print-reportcard-aux x-sorted elide)))

(define vl-reportcard-to-string ((x vl-reportcard-p)
                                 &key
                                 ((elide maybe-natp) '3))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (vl-reportcard)
  :short "Pretty-print a @(see vl-reportcard-p) into a string."
  :long "<p>See also @(see vl-print-reportcard).</p>"
  (with-local-ps (vl-print-reportcard x :elide elide)))

(defsection vl-trace-warnings
  :parents (warnings)
  :short "Pretty-print warnings as they are created."
  :long "<p>This is a debugging aide.  Usage is:</p>

@({
    ACL2 !> (vl::vl-trace-warnings)
})

<p>This just traces @(see make-vl-warning) in a fancy way so that warnings are
pretty-printed to the terminal, automatically, whenever they are constructed.
This may be useful, along with other debugging output, for figuring out why
some warning is being constructed.</p>

<p>This is just a macro based on @(see trace$).  You can turn off warning
tracing using @(see untrace$).</p>"

  (defmacro vl-trace-warnings ()
    `(trace$ (vl-warning :entry (list 'make-vl-warning)
                         :exit (list 'make-vl-warning
                                     (with-local-ps (vl-print-warning acl2::value)))))))

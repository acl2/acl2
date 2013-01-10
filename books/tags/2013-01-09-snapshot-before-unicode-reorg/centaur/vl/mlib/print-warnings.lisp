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
(include-book "warnings")
(include-book "fmt")
(local (include-book "../util/arithmetic"))


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
                            (cat " (fatal, from " (str::downcase-string (symbol-name fn)) ")"))
                           (fatalp
                            " (fatal)")
                           (fn
                            (cat " (from " (str::downcase-string (symbol-name fn)) ")"))
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
                   (rchars (str::revappend-chars (natstr (- len limit)) rchars))
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
                         (t (cat (natstr (len x)) " Warnings")))))
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

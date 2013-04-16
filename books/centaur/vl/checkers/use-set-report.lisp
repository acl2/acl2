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
(include-book "../mlib/writer")
(include-book "../mlib/print-warnings")
(include-book "../util/string-alists")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(defaggregate vl-useset-report-entry

; In addition to annotating the wires of each module, we can generate a
; use-set report as an object that more concisely captures our analysis
; for each module.  It is relatively convenient to print such reports.

; It is convenient for name to come first, so that sorting with mergesort
; orders the report by module name.

  :parents (use-set)
  :tag :vl-useset-report

  ((name     stringp :rule-classes :type-prescription)
   (spurious string-listp)
   (unused   string-listp)
   (unset    string-listp)
   (wwires   string-listp)
   (warnings vl-warninglist-p)
   (typos    ;; alist from typo detector
    (and (alistp typos)
         (vl-string-keys-p typos)
         (vl-string-list-values-p typos)))
   ;; mismatches -- active high/low mismatches, this stuff never worked well
   ;; backward-flow into inputs
   (lvalue-inputs string-listp)))

(deflist vl-useset-report-p (x)
  (vl-useset-report-entry-p x)
  :elementp-of-nil nil)


(define vl-split-useset-report ((x     vl-useset-report-p)
                                (fine  string-listp)
                                (probs vl-useset-report-p))
  :returns (mv (fine  string-listp
                      "Names of modules with no problems."
                      :hyp :fguard)
               (probs vl-useset-report-p
                      "Subset of X that actually has problems."
                      :hyp :fguard))

; Many modules do not have any unused or unset wires.  Rather than verbosely
; include these in the report, we would like to throw them away and only keep
; the modules for which we have identified some problems.

; This function walks over the report and accumulates into FINE the names of
; any modules for which we have nothing to report, and into PROBS the names of
; any modules for which we have something to report.

  (b* (((when (atom x))
        (mv fine probs))
       (entry      (car x))
       (name       (vl-useset-report-entry->name entry))
       (spurious   (vl-useset-report-entry->spurious entry))
       (unused     (vl-useset-report-entry->unused entry))
       (unset      (vl-useset-report-entry->unset entry))
       (warnings   (vl-useset-report-entry->warnings entry))
       (wwires     (vl-useset-report-entry->wwires entry))
       (lvalue-inputs (vl-useset-report-entry->lvalue-inputs entry))
       (finep      (and (null spurious)
                        (null unused)
                        (null unset)
                        (null wwires)
                        (null lvalue-inputs)
                        (atom warnings))))
    (vl-split-useset-report (cdr x)
                            (if finep (cons name fine) fine)
                            (if finep probs (cons entry probs)))))

(define vl-star-names-of-warning-wires ((x             string-listp)
                                        (warning-wires string-listp))
  :returns (new-x string-listp :hyp (force (string-listp x)))
  :short "Change names in @('x') by putting a @('*') in front of any name that
is among the @('warning-wires')."
  (cond ((atom x)
         nil)
        ((member-equal (car x) warning-wires)
         (cons (cat (car x) "*")
               (vl-star-names-of-warning-wires (cdr x) warning-wires)))
        (t
         (cons (car x)
               (vl-star-names-of-warning-wires (cdr x) warning-wires)))))

(define vl-report-totals ((report vl-useset-report-p))
  :returns (mv (num-spurious natp :rule-classes :type-prescription)
               (num-unused   natp :rule-classes :type-prescription)
               (num-unset    natp :rule-classes :type-prescription)
               (num-linputs  natp :rule-classes :type-prescription))
  (if (atom report)
      (mv 0 0 0 0)
    (b* ((spurious1 (len (vl-useset-report-entry->spurious (car report))))
         (unused1   (len (vl-useset-report-entry->unused (car report))))
         (unset1    (len (vl-useset-report-entry->unset (car report))))
         (linputs1  (len (vl-useset-report-entry->lvalue-inputs (car report))))
         ((mv spurious2 unused2 unset2 linputs2)
          (vl-report-totals (cdr report))))
      (mv (+ spurious1 spurious2)
          (+ unused1 unused2)
          (+ unset1 unset2)
          (+ linputs1 linputs2)))))

(define vl-print-typo-possibilities ((x string-listp) &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((vl-ps->htmlp)
         (vl-ps-seq (vl-print-markup "<tt>")
                    (vl-print (car x))
                    (vl-print-markup "</tt>")
                    (cond ((and (consp (cdr x))
                                (consp (cddr x)))
                           ;; At least two more things.
                           (vl-print ", "))
                          ((consp (cdr x))
                           ;; Next one is the last thing.
                           (vl-print ", or "))
                          (t
                           ;; This was already the last thing.
                           (vl-print "?")))
                    (vl-print-typo-possibilities (cdr x))))
        (t
         (vl-ps-seq (vl-print (car x))
                    (if (consp (cdr x))
                        (vl-print ", ")
                      ps)
                    (vl-print-typo-possibilities (cdr x))))))

(define vl-print-typo-alist ((x (and (alistp x)
                                     (vl-string-keys-p x)
                                     (vl-string-list-values-p x)))
                             &key (ps 'ps))
  (cond ((atom x)
         ps)
        ((vl-ps->htmlp)
         (vl-ps-seq (vl-print-markup "<li>Should <tt class=\"typo_w\">")
                    (vl-print (caar x))
                    (vl-print-markup "</tt> be ")
                    (vl-print-typo-possibilities (cdar x))
                    (vl-println-markup "</li>")
                    (vl-print-typo-alist (cdr x))))
        (t
         (vl-ps-seq (vl-print "  ")
                    (vl-print (caar x))
                    (vl-print ": ")
                    (vl-indent 30)
                    (vl-print-typo-possibilities (cdar x))
                    (vl-println "")
                    (vl-print-typo-alist (cdr x))))))

(define vl-print-useset-report-entry ((entry vl-useset-report-entry-p)
                                      include-namep
                                      suppress-spuriousp
                                      suppress-unusedp
                                      suppress-unsetp
                                      suppress-typosp
                                      suppress-linputsp
                                      suppress-warningsp
                                      &key (ps 'ps))

; This prints an individual entry in the use-set report.  In HTML mode, this
; function is used for two purposes:
;
;   - To generate an individual report for a particular module, and
;   - To generate a full report covering all of the modules.
;
; If we are dealing with a single module, we do not want to include the name of
; the module and a link to it, because we are already on that page, so we set
; include-namep to nil.  On the other hand, for a full report we do want to go
; ahead and include the names with links.

  (b* ((htmlp        (vl-ps->htmlp))
       (name         (vl-useset-report-entry->name entry))
       ((when (equal name "mp_verror"))
        (vl-cw "Skipping mp_verror module~%~%"))
       (spurious     (vl-useset-report-entry->spurious entry))
       (unused       (vl-useset-report-entry->unused entry))
       (unset        (vl-useset-report-entry->unset entry))
       (typos        (vl-useset-report-entry->typos entry))
       (linputs      (vl-useset-report-entry->lvalue-inputs entry))
       (num-spurious (len spurious))
       (num-unused   (len unused))
       (num-unset    (len unset))
       (num-linputs  (len linputs))
       (warnings     (vl-useset-report-entry->warnings entry))
       (warnings     (vl-remove-warnings '(:vl-warn-ifxz :vl-warn-noports) warnings))
       (wwires       (vl-useset-report-entry->wwires entry))
       (spurious*    (vl-star-names-of-warning-wires spurious wwires))
       (unused*      (vl-star-names-of-warning-wires unused wwires))
       (unset*       (vl-star-names-of-warning-wires unset wwires))

       (show-linputs     (and* linputs     (not* suppress-linputsp)))
       (show-spurious    (and* spurious    (not* suppress-spuriousp)))
       (show-unused      (and* unused      (not* suppress-unusedp)))
       (show-unset       (and* unset       (not* suppress-unsetp)))
       (show-typos       (and* typos       (not* suppress-typosp)))
       (show-warnings    (and* warnings    (not* suppress-warningsp)))
       (show-anything    (or* show-linputs
                              show-spurious
                              show-unused
                              show-unset
                              show-typos
                              show-warnings)))

    (if (not htmlp)

        (vl-ps-seq
         (if show-anything
             (vl-cw "Module ~s0 -- ~x1 spurious, ~x2 unused and ~x3 unset wires.~%"
                    name num-spurious num-unused num-unset)
           ps)
         (if show-linputs
             (vl-ps-seq (vl-print "Inputs used like inouts: (")
                        (vl-print num-linputs)
                        (vl-println "):")
                        (vl-print-strings-with-commas linputs 3)
                        (vl-println ""))
           ps)
         (if show-spurious
             (vl-ps-seq (vl-println " Spurious wires:")
                        (vl-print-strings-with-commas spurious* 3)
                        (vl-println ""))
           ps)
         (if show-unused
             (vl-ps-seq (vl-println " Unused wires:")
                        (vl-print-strings-with-commas unused* 3)
                        (vl-println ""))
           ps)
         (if show-unset
             (vl-ps-seq (vl-println " Unset wires:")
                        (vl-print-strings-with-commas unset* 3)
                        (vl-println ""))
           ps)
         (if show-typos
             (vl-ps-seq (vl-println " Possible typos:")
                        (vl-print-typo-alist typos)
                        (vl-println ""))
           ps)

         (if show-warnings
             (vl-ps-seq (vl-println " Warnings:")
                        (vl-print-warnings warnings)
                        (vl-println ""))
           ps)
         (if show-anything
             (vl-println "")
           ps))

      (vl-ps-seq
       (if (not show-anything)
           ps
         (vl-ps-seq
          (vl-println-markup "<div class=\"vl_use_set_report\">")
          (vl-println-markup "<dl>")

          (if (not* include-namep)
              ps
            (vl-ps-seq (vl-println-markup "<dt class=\"vl_useset_report_title\">")
                       (vl-print-markup "<a href=\"javascript:showModule('")
                       (vl-print-url name)
                       (vl-print-markup "')\">")
                       (vl-print name)
                       (vl-print-markup "</a></dt>")))))

       (if (and* show-linputs (or* linputs (not* include-namep)))
           (vl-ps-seq
            (vl-println-markup (if linputs
                                   "<dt class=\"vl_yes_linputs\">"
                                 "<dt class=\"vl_no_linputs\">"))
            (vl-print num-linputs)
            (vl-print (if (= num-linputs 1)
                          " Input used like inout:"
                        " Inputs used like inouts:"))
            (vl-println-markup "</dt>")
            (vl-println-markup "<dd>")
            (vl-print-strings-with-commas linputs 0)
            (vl-println-markup "</dd>"))
         ;; Else, this is the full report (because we're including names),
         ;; and there is nothing spurious to report.  Don't make it chatty.
         ps)


       (if (and* show-spurious (or* spurious (not include-namep)))
           (vl-ps-seq
            (vl-println-markup (if spurious
                                   "<dt class=\"vl_yes_spurious\">"
                                 "<dt class=\"vl_no_spurious\">"))
            (vl-print num-spurious)
            (vl-print " Spurious ")
            (vl-print (if (= num-spurious 1) "Wire" "Wires"))
            (vl-println-markup "</dt>")
            (vl-print-markup "<dd>")
            (vl-print-strings-with-commas spurious* 0)
            (vl-println-markup "</dd>"))
         ;; As above.
         ps)

       (if (and* show-unused (or* unused (not include-namep)))
           (vl-ps-seq
            (vl-println-markup (if unused
                                   "<dt class=\"vl_yes_unused\">"
                                 "<dt class=\"vl_no_unused\">"))
            (vl-print num-unused)
            (vl-print " Unused ")
            (vl-print (if (= num-unused 1) "Wire" "Wires"))
            (vl-println-markup "</dt>")
            (vl-print-markup "<dd>")
            (vl-print-strings-with-commas unused* 0)
            (vl-println-markup "</dd>"))
         ;; As above
         ps)

       (if (and* show-unset (or* unset (not include-namep)))
           (vl-ps-seq
            (vl-println-markup (if unset
                                   "<dt class=\"vl_yes_unset\">"
                                 "<dt class=\"vl_no_unset\">"))
            (vl-print num-unset)
            (vl-print " Unset ")
            (vl-print (if (= num-unset 1) "Wire" "Wires"))
            (vl-println-markup "</dt>")
            (vl-print-markup "<dd>")
            (vl-print-strings-with-commas unset* 0)
            (vl-println-markup "</dd>"))
         ;; As above
         ps)

       (if (or* (not show-typos) (not typos))
           ps
         (vl-ps-seq
          (vl-println-markup "<dt class=\"vl_yes_typos\">Possible Typos</dt>")
          (vl-println-markup "<dd><ul class=\"typo_list\">")
          (vl-print-typo-alist typos)
          (vl-println-markup "</ul></dd>")))

       (if (and* show-warnings warnings)
           (vl-print-warnings warnings)
         ps)

       (if show-anything
           (vl-println-markup "</div>")
         ps)))))


(define vl-print-useset-report-full-aux ((x vl-useset-report-p)
                                         suppress-spuriousp
                                         suppress-unusedp
                                         suppress-unsetp
                                         suppress-typosp
                                         suppress-linputsp
                                         suppress-warningsp
                                         &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-print-useset-report-entry (car x) t
                                             suppress-spuriousp
                                             suppress-unusedp
                                             suppress-unsetp
                                             suppress-typosp
                                             suppress-linputsp
                                             suppress-warningsp)
               (vl-print-useset-report-full-aux (cdr x)
                                                suppress-spuriousp
                                                suppress-unusedp
                                                suppress-unsetp
                                                suppress-typosp
                                                suppress-linputsp
                                                suppress-warningsp))))

(define vl-print-useset-report-top ((x            vl-useset-report-p)
                                    (mpv-warnings vl-warninglist-p)
                                    suppress-spuriousp
                                    suppress-unusedp
                                    suppress-unsetp
                                    suppress-typosp
                                    suppress-linputsp
                                    suppress-warningsp
                                    &key (ps 'ps))
  (b* ((htmlp           (vl-ps->htmlp))
       ((mv fine probs) (vl-split-useset-report x nil nil))
       (fine            (mergesort fine))
       (probs           (mergesort probs))
       ((mv spurious unused unset linputs) (vl-report-totals probs)))

    (if (not htmlp)

        ;; TEXT Mode.
        (vl-ps-seq
         (vl-cw "--- REPORT BEGINS HERE -------------------------~%")

         (vl-cw "~%~x0 warning(s) for mp_verror:~%~%" (len mpv-warnings))
         (if (atom mpv-warnings)
             ps
           (vl-ps-seq
            (vl-print-warnings mpv-warnings)
            (vl-println "")
            (vl-println "")))

         (vl-cw "~%~%~x0 modules have a total of: ~% ~
                         - ~x1 spurious wires, ~% ~
                         - ~x2 unused wires, ~% ~
                         - ~x3 unset wires, and ~% ~
                         - ~x4 inputs used like inouts, ~%~%"
                (length probs) spurious unused unset linputs)

         (vl-print-useset-report-full-aux probs
                                          suppress-spuriousp
                                          suppress-unusedp
                                          suppress-unsetp
                                          suppress-typosp
                                          suppress-linputsp
                                          suppress-warningsp)
         (vl-cw "~x0 modules look fine (no wires to report):~%~%" (length fine))
         (vl-print-strings-with-commas fine 3)
         (vl-println "")
         (vl-cw "--- REPORT ENDS HERE ---------------------------~%~%"))

      ;; HTML Mode.
      (vl-ps-seq
       (vl-println-markup "<div class=\"vl_use_set_full_report\">")

;               (vl-print-markup "<h4 class=\"vl_use_set_prob_head\">")
;               (vl-print (len mpv-warnings))
;               (vl-print " warning(s) for mp_verror")
;               (vl-println-markup "</h4>")
;               (if (atom mpv-warnings)
;                   ps
;                 (vl-print-warnings mpv-warnings))

       (vl-print-markup "<h4 class=\"vl_use_set_prob_head\">")
       (vl-print (len probs))
       (vl-print-markup " modules have a total of <b>")
       (vl-print spurious)
       (vl-print-markup "</b> spurious, <b>")
       (vl-print unused)
       (vl-print-markup "</b> unused, and <b>")
       (vl-print unset)
       (vl-println-markup "</b> unset wires</h4>")
       (vl-println-markup "<div class=\"vl_use_set_prob_list\">")
       (vl-print-useset-report-full-aux probs
                                        suppress-spuriousp
                                        suppress-unusedp
                                        suppress-unsetp
                                        suppress-typosp
                                        suppress-linputsp
                                        suppress-warningsp)
       (vl-println-markup "</div></div>")

;               (vl-print-markup "<h4 class=\"vl_use_set_fine_head\">")
;               (vl-print (length fine))
;               (vl-println-markup " modules have no spurious, unused, or unset wires</h4>")
;               (vl-print-markup "<dl class=\"vl_use_set_fine_list\"><dd>")
;               (vl-print-strings-with-commas fine 0)
;               (vl-println-markup "</dd></dl>")
       (vl-println-markup "</div>")))))


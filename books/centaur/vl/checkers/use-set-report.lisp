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
(include-book "../mlib/warnings")
;(include-book "../transforms/xf-cross-active")
(include-book "../util/string-alists")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(defaggregate vl-useset-report-entry

; In addition to annotating the wires of each module, we can generate a
; use-set report as an object that more concisely captures our analysis
; for each module.  It is relatively convenient to print such reports.

; It is convenient for name to come first, so that sorting with mergesort
; orders the report by module name.

  (name spurious unused unset wwires warnings typos mismatches
        lvalue-inputs)
  :tag :vl-useset-report
  :parents (use-set)
  :require ((stringp-of-vl-useset-report->name            (stringp name))
            (string-listp-of-vl-useset-report->spurious   (string-listp spurious))
            (string-listp-of-vl-useset-report->unused     (string-listp unused))
            (string-listp-of-vl-useset-report->unset      (string-listp unset))
            (string-listp-of-vl-useset-report->wwires     (string-listp wwires))
            (vl-warninglist-p-of-vl-useset-report->wwires (vl-warninglist-p warnings))
            ;; Alist from typo detector
            (alistp-of-vl-useset-report->typos                  (alistp typos))
            (vl-string-keys-p-of-vl-useset-report->typos        (vl-string-keys-p typos))
            (vl-string-list-values-p-of-vl-useset-report->typos (vl-string-list-values-p typos))

; this stuff never worked
;            ;; Active high/low mismatches
;            (vl-activemismatchlist-p-of-vl-useset-report->mismatches
;             (vl-activemismatchlist-p mismatches))

            ;; Backward flow into inputs
            (string-listp-of-vl-useset-report->lvalue-inputs (string-listp lvalue-inputs))
            ))

(deflist vl-useset-report-p (x)
  (vl-useset-report-entry-p x)
  :elementp-of-nil nil)


(defund vl-split-useset-report (x fine probs)
  "Returns (MV FINE PROBS)"
  (declare (xargs :guard (and (vl-useset-report-p x)
                              (string-listp fine)
                              (vl-useset-report-p probs))))

; Many modules do not have any unused or unset wires.  Rather than verbosely
; include these in the report, we would like to throw them away and only keep
; the modules for which we have identified some problems.

; This function walks over the report and accumulates into FINE the names of
; any modules for which we have nothing to report, and into PROBS the names of
; any modules for which we have something to report.

  (if (atom x)
      (mv fine probs)
    (let* ((entry      (car x))
           (name       (vl-useset-report-entry->name entry))
           (spurious   (vl-useset-report-entry->spurious entry))
           (unused     (vl-useset-report-entry->unused entry))
           (unset      (vl-useset-report-entry->unset entry))
           (warnings   (vl-useset-report-entry->warnings entry))
           (wwires     (vl-useset-report-entry->wwires entry))
           (mismatches (vl-useset-report-entry->mismatches entry))
           (lvalue-inputs (vl-useset-report-entry->lvalue-inputs entry))
           (finep      (and (null spurious)
                            (null unused)
                            (null unset)
                            (null wwires)
                            (null lvalue-inputs)
                            (atom mismatches)
                            (atom warnings))))
      (vl-split-useset-report (cdr x)
                              (if finep (cons name fine) fine)
                              (if finep probs (cons entry probs))))))

(defthm string-listp-of-vl-split-useset-report
  (implies (and (force (vl-useset-report-p x))
                (force (string-listp fine)))
           (string-listp (mv-nth 0 (vl-split-useset-report x fine probs))))
  :hints(("Goal" :in-theory (enable vl-split-useset-report))))

(defthm vl-useset-report-p-of-vl-split-useset-report
  (implies (and (force (vl-useset-report-p x))
                (force (vl-useset-report-p probs)))
           (vl-useset-report-p (mv-nth 1 (vl-split-useset-report x fine probs))))
  :hints(("Goal" :in-theory (enable vl-split-useset-report))))




(defund vl-star-names-of-warning-wires (x warning-wires)
  (declare (xargs :guard (and (string-listp x)
                              (string-listp warning-wires))))

; For each string s in X, if s is also among the warning wires, put a * at the
; end of its name.

  (cond ((atom x)
         nil)
        ((member-equal (car x) warning-wires)
         (cons (str::cat (car x) "*")
               (vl-star-names-of-warning-wires (cdr x) warning-wires)))
        (t
         (cons (car x)
               (vl-star-names-of-warning-wires (cdr x) warning-wires)))))

(defthm string-listp-of-vl-star-names-of-warning-wires
  (implies (force (string-listp x))
           (string-listp (vl-star-names-of-warning-wires x warning-wires)))
  :hints(("Goal" :in-theory (enable vl-star-names-of-warning-wires))))


(defsection vl-report-totals

  (defund vl-report-totals (report)
    "Returns (MV NUM-SPURIOUS NUM-UNUSED NUM-UNSET NUM-MISMATCH NUM-LINPUTS)"
    (declare (xargs :guard (vl-useset-report-p report)))
    (if (atom report)
        (mv 0 0 0 0 0)
      (b* ((spurious1 (length (vl-useset-report-entry->spurious (car report))))
           (unused1   (length (vl-useset-report-entry->unused (car report))))
           (unset1    (length (vl-useset-report-entry->unset (car report))))
           (mismatch1 (len (vl-useset-report-entry->mismatches (car report))))
           (linputs1  (length (vl-useset-report-entry->lvalue-inputs (car report))))
           ((mv spurious2 unused2 unset2 mismatch2 linputs2)
            (vl-report-totals (cdr report))))
          (mv (+ spurious1 spurious2)
              (+ unused1 unused2)
              (+ unset1 unset2)
              (+ mismatch1 mismatch2)
              (+ linputs1 linputs2)))))

  (local (in-theory (e/d (vl-report-totals)
                         ((force)))))

  (defthm natp-of-vl-report-totals-0
    (natp (mv-nth 0 (vl-report-totals report)))
    :rule-classes :type-prescription)

  (defthm natp-of-vl-report-totals-1
    (natp (mv-nth 1 (vl-report-totals report)))
    :rule-classes :type-prescription)

  (defthm natp-of-vl-report-totals-2
    (natp (mv-nth 2 (vl-report-totals report)))
    :rule-classes :type-prescription)

  (defthm natp-of-vl-report-totals-3
    (natp (mv-nth 3 (vl-report-totals report)))
    :rule-classes :type-prescription)

  (defthm natp-of-vl-report-totals-4
    (natp (mv-nth 4 (vl-report-totals report)))
    :rule-classes :type-prescription))



(defpp vl-print-typo-possibilities (x)
  :guard (string-listp x)
  :body
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

(defpp vl-print-typo-alist (x)
  :guard (and (alistp x)
              (vl-string-keys-p x)
              (vl-string-list-values-p x))
  :body
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




(defund binary-and* (x y)
  (declare (xargs :guard t))
  (if x y nil))

(defund and*-macro (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         t)
        ((atom (cdr x))
         (car x))
        (t
         `(binary-and* ,(car x)
                       ,(and*-macro (cdr x))))))

(defmacro and* (&rest args)
  (and*-macro args))

(add-binop and* binary-and*)


;; (thm (equal (and* x y)
;;             (and x y))
;;      :hints(("Goal" :in-theory (enable binary-and*))))

;; (thm (equal (and* x y z)
;;             (and x y z))
;;      :hints(("Goal" :in-theory (enable binary-and*))))

;; (thm (equal (and* x y z w)
;;             (and x y z w))
;;      :hints(("Goal" :in-theory (enable binary-and*))))


(defund binary-or* (x y)
  (declare (xargs :guard t))
  (if x x y))

(defund or*-macro (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (car x))
        (t
         `(binary-or* ,(car x)
                      ,(or*-macro (cdr x))))))

(defmacro or* (&rest args)
  (or*-macro args))

(add-binop or* binary-or*)


;; (thm (equal (or* x y)
;;             (or x y))
;;      :hints(("Goal" :in-theory (enable binary-or*))))

;; (thm (equal (or* x y z)
;;             (or x y z))
;;      :hints(("Goal" :in-theory (enable binary-or*))))

;; (thm (equal (or* x y z w)
;;             (or x y z w))
;;      :hints(("Goal" :in-theory (enable binary-or*))))




(defund not* (x)
  (declare (xargs :guard t))
  (not x))

(defpp vl-print-useset-report-entry (entry include-namep
                                           suppress-spuriousp
                                           suppress-unusedp
                                           suppress-unsetp
                                           suppress-typosp
;                                           suppress-mismatchesp
                                           suppress-linputsp
                                           suppress-warningsp)

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

  :guard (vl-useset-report-entry-p entry)
  :body (b* ((htmlp        (vl-ps->htmlp))
             (name         (vl-useset-report-entry->name entry))
             ((when (equal name "mp_verror"))
              (vl-cw "Skipping mp_verror module~%~%"))
             (spurious     (vl-useset-report-entry->spurious entry))
             (unused       (vl-useset-report-entry->unused entry))
             (unset        (vl-useset-report-entry->unset entry))
             (typos        (vl-useset-report-entry->typos entry))
;             (mismatches   (vl-useset-report-entry->mismatches entry))
             (linputs      (vl-useset-report-entry->lvalue-inputs entry))
             (num-spurious (length spurious))
             (num-unused   (length unused))
             (num-unset    (length unset))
;             (num-mismatch (len mismatches))
             (num-linputs  (length linputs))
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
;             (show-mismatches  (and* mismatches  (not* suppress-mismatchesp)))
             (show-warnings    (and* warnings    (not* suppress-warningsp)))
             (show-anything    (or* show-linputs
                                    show-spurious
                                    show-unused
                                    show-unset
                                    show-typos
;                                    show-mismatches
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

; this stuff never worked
;                 (if show-mismatches
;                     (vl-ps-seq (vl-println " Possible sense mismatches:")
;                                (vl-pp-activemismatchlist mismatches)
;                                (vl-println ""))
;                   ps)

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


; this stuff never worked
;               (if (or* (not show-mismatches) (not mismatches))
;                   ps
;                 (vl-ps-seq
;                  (vl-print-markup "<dt class=\"vl_yes_mismatches\">")
;                  (vl-print num-mismatch)
;                  (vl-print " Possible Sense Mismatches")
;                  (vl-println-markup "</dt>")
;                  (vl-println-markup "<dd>")
;                  (vl-pp-activemismatchlist mismatches)
;                  (vl-println-markup "</dd>")
;                  (vl-println-markup "</dt>")))

               (if (and* show-warnings warnings)
                   (vl-print-warnings warnings)
                 ps)

               (if show-anything
                   (vl-println-markup "</div>")
                 ps)))))


(defpp vl-print-useset-report-full-aux (x suppress-spuriousp
                                          suppress-unusedp
                                          suppress-unsetp
                                          suppress-typosp
;                                          suppress-mismatchesp
                                          suppress-linputsp
                                          suppress-warningsp)
  :guard (vl-useset-report-p x)
  :body (if (atom x)
            ps
          (vl-ps-seq (vl-print-useset-report-entry (car x) t
                                                   suppress-spuriousp
                                                   suppress-unusedp
                                                   suppress-unsetp
                                                   suppress-typosp
;                                                   suppress-mismatchesp
                                                   suppress-linputsp
                                                   suppress-warningsp)
                     (vl-print-useset-report-full-aux (cdr x)
                                                      suppress-spuriousp
                                                      suppress-unusedp
                                                      suppress-unsetp
                                                      suppress-typosp
;                                                      suppress-mismatchesp
                                                      suppress-linputsp
                                                      suppress-warningsp))))

(defpp vl-print-useset-report-top (x mpv-warnings
                                     suppress-spuriousp
                                     suppress-unusedp
                                     suppress-unsetp
                                     suppress-typosp
;                                     suppress-mismatchesp
                                     suppress-linputsp
                                     suppress-warningsp)
  :guard (and (vl-useset-report-p x)
              (vl-warninglist-p mpv-warnings))
  :body (b* ((htmlp           (vl-ps->htmlp))
             ((mv fine probs) (vl-split-useset-report x nil nil))
             (fine            (mergesort fine))
             (probs           (mergesort probs))
             ((mv spurious unused unset mismatch linputs) (vl-report-totals probs)))

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
                         - ~x4 inputs used like inouts, and ~% ~
                         - ~x5 potential sense mismatches.~%~%"
                        (length probs) spurious unused unset mismatch linputs)

                 (vl-print-useset-report-full-aux probs
                                                  suppress-spuriousp
                                                  suppress-unusedp
                                                  suppress-unsetp
                                                  suppress-typosp
;                                                  suppress-mismatchesp
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
;                                                suppress-mismatchesp
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


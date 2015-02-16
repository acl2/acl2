; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "../loader/descriptions")
(include-book "../loader/inject-comments")
(include-book "../util/print")
(local (include-book "../util/arithmetic"))


; Location display.
;
; When the user clicks on a particular location, we want to display a nice
; page that essentially shows something like this:
;
;  module mod ( ... );    } "startline"
;
;  ...                    } "hidden before context"  (HBC)
;
;  wire w;                } "before" context    (BC)
;  wire v;                }
;
;  assign w = ... ;       } "goal line"
;
;  assign v = ... ;       } "after context" (AC)
;  assign q = ... ;       }
;
;  ...                    } "hidden after context" (HAC)
;
;  endmodule              } "lastline"


(define vl-find-description-for-loc ((loc vl-location-p)
                                     (x   vl-descriptionlist-p))
  :returns (desc (iff (vl-description-p desc)
                      desc))
  ;; Find the first module that contains the desired location.
  (cond ((atom x)
         nil)
        ((vl-location-between-p loc
                                (vl-description->minloc (car x))
                                (vl-description->maxloc (car x)))
         (vl-description-fix (car x)))
        (t
         (vl-find-description-for-loc loc (cdr x)))))


(define vls-showloc-print-bc (contents start goal &key (ps 'ps))
  ;; Assumes the starting line has already been printed
  :guard (and (stringp contents)
              (posp start)
              (posp goal))
  ;; The before-context is everything between start and goal, exclusive.
  (b* ((bc-start  (+ 1 start))
       (bc-stop   (- goal 1))
       (bc-nlines (+ 1 (- goal bc-start))))
    (cond
     ((< bc-stop bc-start)
      ;; There's no before context at all, so there's nothing to print.
      ps)

     ((<= bc-nlines 5)
      ;; The before-context is pretty small, so don't hide any of it.
      (vl-ps-seq
       (vl-println-markup "<div id=\"showloc_bc\">")
       (vl-print (str::strlines bc-start bc-stop contents))
       (vl-println-markup "</div>")))

     (t
      ;; The before-context is pretty large.
      (vl-ps-seq
       (vl-println-markup "  <a id=\"showloc_hbc_link\" href=\"javascript:void(0)\" onclick=\"showloc_hbc()\">...</a>")
       (vl-println-markup "<div id=\"showloc_hbc\" style=\"display: none\">")
       (vl-print (str::strlines bc-start (- bc-stop 4) contents))
       (vl-println-markup "</div>") ;
       (vl-println-markup "<div id=\"showloc_bc\">")
       (vl-print (str::strlines (- bc-stop 3) bc-stop contents))
       (vl-println-markup "</div>"))))))

(define vls-showloc-print-ac (contents goal end &key (ps 'ps))
  ;; Assumes everything up through and including the goal line have already
  ;; been printed.
  :guard (and (stringp contents)
              (posp goal)
              (posp end))
  ;; The after-context is everything between goal and end, exclusive.
  (b* ((ac-start (+ goal 1))
       (ac-stop  (- end 1))
       (ac-nlines (+ 1 (- end ac-start))))
      (cond
       ((< ac-stop ac-start)
        ;; No after-context, so nothing to print
        ps)

       ((<= ac-nlines 5)
        ;; The before-context is pretty small, so don't hide any of it.
        (vl-ps-seq
         (vl-println-markup "<div id=\"showloc_ac\">")
         (vl-print (str::strlines ac-start ac-stop contents))
         (vl-println-markup "</div>")))

       (t
        ;; The before-context is pretty large.
        (vl-ps-seq
         (vl-println-markup "<div id=\"showloc_ac\">")
         (vl-print (str::strlines ac-start (+ ac-start 3) contents))
         (vl-println-markup "</div>")
         (vl-println-markup "<a id=\"showloc_hac_link\" href=\"javascript:void(0)\" onClick=\"showloc_hac()\">...</a>")
         (vl-println-markup "<div id=\"showloc_hac\" style=\"display: none\">")
         (vl-print (str::strlines (+ ac-start 4) ac-stop contents))
         (vl-println-markup "</div>")
         )))))

(define vls-showloc-print-goal (line col &key (ps 'ps))
  :guard (and (stringp line)
              (natp col))
  (vl-ps-seq
   (vl-println-markup "<div id=\"showloc_goal\">")
   (vl-println-markup "<a name=\"hac_goal\">")
   (let ((len (length line)))
     (if (>= col len)
         ;; Really this is an error, there's no such column on the goal line.
         ;; We'll just print whatever the line is.
         (vl-println line)
       (vl-ps-seq
        (vl-print (subseq line 0 col))
        (vl-print-markup "<span class=\"showloc_goalcol\">")
        (vl-print (char line col))
        (vl-print-markup "</span>")
        (vl-println (subseq line (+ col 1) nil)))))
   (vl-println-markup "</a>")
   (vl-println-markup "</div>")))

(define vls-showloc-print (contents min max line col &key (ps 'ps))
  :guard (and (stringp contents)
              (posp min)
              (posp max)
              (posp line)
              (natp col))
  (vl-ps-seq
   (if (equal min line)
       ps
     (vl-ps-seq (vl-println-markup "<div id=\"showloc_start\">")
                (vl-println (str::strline min contents))
                (vl-println-markup "</div>")))
   (vls-showloc-print-bc contents min line)
   (vls-showloc-print-goal (str::strline line contents) col)
   (vls-showloc-print-ac contents line max)
   (if (equal max line)
       ps
     (vl-ps-seq (vl-println-markup "<div id=\"showloc_end\">")
                (vl-println (str::strline max contents))
                (vl-println-markup "</div>")))))


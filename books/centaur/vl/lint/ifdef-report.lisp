; VL Lint - Ifdef Usage Report
; Copyright (C) 2018 Apple, Inc.
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
; Original author: Jared Davis

(in-package "VL")
(include-book "../loader/preprocessor/defines")
(include-book "../mlib/writer")
(include-book "../mlib/json")
(local (include-book "../util/arithmetic"))

(define vl-clean-ifdef-map ((x vl-ifdef-use-map-p))
  :returns (cleaned-x vl-ifdef-use-map-p)
  :measure (len (vl-ifdef-use-map-fix x))
  (b* ((x (vl-ifdef-use-map-fix x))
       ((when (atom x))
        nil)
       ((cons name uses) (car x)))
    (cons (cons name (mergesort uses))
          (vl-clean-ifdef-map (cdr x)))))

(define vl-print-ifdef-brief-summary ((x vl-ifdef-use-map-p) &key (ps 'ps))
  :measure (len (vl-ifdef-use-map-fix x))
  (b* ((x (vl-ifdef-use-map-fix x))
       ((when (atom x))
        ps)
       ((cons name uses) (car x)))
    (vl-ps-seq (vl-indent 4)
               (vl-print (len uses))
               (vl-indent 20)
               (vl-print " ")
               (vl-print-str name)
               (vl-println "")
               (vl-print-ifdef-brief-summary (cdr x)))))

(define vl-print-ifdef-context ((x vl-ifdef-context-p) &key (ps 'ps))
  (b* (((vl-ifdef-context x)))
    (vl-ps-seq (vl-indent 8)
               (vl-print-loc x.loc)
               (vl-println ""))))

(define vl-print-ifdef-context-list ((x vl-ifdef-context-list-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-print-ifdef-context (car x))
               (vl-print-ifdef-context-list (cdr x)))))

(define vl-print-ifdef-long-report ((x vl-ifdef-use-map-p) &key (ps 'ps))
  :measure (len (vl-ifdef-use-map-fix x))
  (b* ((x (vl-ifdef-use-map-fix x))
       ((when (atom x))
        ps)
       ((cons name uses) (car x)))
    (vl-ps-seq (vl-print "  - ")
               (vl-print-str name)
               (vl-println "")
               (vl-print-ifdef-context-list uses)
               (vl-print-ifdef-long-report (cdr x)))))

(define vl-print-ifdef-report-main ((ifdefmap vl-ifdef-use-map-p) &key (ps 'ps))
  (b* ((ifdefmap (mergesort (vl-clean-ifdef-map ifdefmap))))
    (vl-ps-seq
      (vl-basic-cw "VL `ifdef report~%")
      (vl-basic-cw "----------------~%")
      (vl-basic-cw "~%")
      (vl-basic-cw "Defines used in `ifdef/`elsif directives:~%~%")
      (vl-print-ifdef-brief-summary ifdefmap)
      (vl-basic-cw "~%~%")
      (vl-basic-cw "Locations where these defines are used:~%~%")
      (vl-print-ifdef-long-report ifdefmap))))

(define vl-write-ifdef-report ((filename stringp)
                               (ifdefmap vl-ifdef-use-map-p)
                               state)
  (with-ps-file filename
    (vl-print-ifdef-report-main ifdefmap)))



;; JSON formatted reports

#| moved to json.lisp with changes..
(define vl-jp-location ((x vl-location-p) &key (ps 'ps))
  (jp-str (vl-location-string x)))

(add-json-encoder vl-location-p vl-jp-location)
|#

(def-vl-jp-list location :newlines 8)

(define vl-split-def-contextlist ((x        vl-def-context-list-p)
                                  (active   vl-locationlist-p)
                                  (inactive vl-locationlist-p))
  :returns (mv (active   vl-locationlist-p)
               (inactive vl-locationlist-p))
  (b* ((active   (vl-locationlist-fix active))
       (inactive (vl-locationlist-fix inactive))
       ((when (atom x))
        (mv active inactive))
       ((vl-def-context x1) (first x))
       ((when x1.activep)
        (vl-split-def-contextlist (rest x) (cons x1.loc active) inactive)))
    (vl-split-def-contextlist (rest x) active (cons x1.loc inactive))))

(defprojection vl-ifdef-context-list->locs ((x vl-ifdef-context-list-p))
  :returns (locs vl-locationlist-p)
  (vl-ifdef-context->loc x))

(local (defrule vl-locationlist-p-of-insert
         (implies (and (vl-locationlist-p x)
                       (vl-location-p a))
                  (vl-locationlist-p (set::insert a x)))
         :enable set::primitive-rules))

(local (defrule vl-locationlist-p-of-mergesort
         (implies (vl-locationlist-p x)
                  (vl-locationlist-p (mergesort x)))))

(define vl-jp-definfo-1 ((x        vl-define-p)
                         (ifdefmap vl-ifdef-use-map-p "Fast alist of all define uses in ifdefs")
                         (defmap   vl-def-use-map-p   "Fast alist of all define uses in non-ifdefs")
                         &key (ps 'ps))
  (b* (((vl-define x))
       (ifdefs (vl-ifdef-context-list->locs (cdr (hons-get x.name ifdefmap))))
       (uses   (cdr (hons-get x.name defmap)))
       ((mv active inactive) (vl-split-def-contextlist uses nil nil)))
    (vl-ps-seq (jp-str x.name)
               (vl-print ":{")
               (jp-str "def")
               (vl-print ":")
               (vl-jp-location x.loc)
               (vl-println ",")

               (vl-indent 6)
               (jp-str "ifdef_uses")
               (vl-print ":")
               (vl-jp-locationlist (mergesort ifdefs))
               (vl-println ",")

               (vl-indent 6)
               (jp-str "active_uses")
               (vl-print ":")
               (vl-jp-locationlist (mergesort active))
               (vl-println ",")

               (vl-indent 6)
               (jp-str "inactive_uses")
               (vl-print ":")
               (vl-jp-locationlist (mergesort inactive))
               (vl-print "}"))))

(define vl-jp-definfo-aux ((defines  vl-defines-p)
                           (ifdefmap vl-ifdef-use-map-p "Already fast")
                           (defmap   vl-def-use-map-p   "Already fast")
                           &key
                           (ps 'ps))
  (if (atom defines)
      ps
    (vl-ps-seq
     (vl-jp-definfo-1 (car defines) ifdefmap defmap)
     (if (consp (cdr defines))
         (vl-println ", ")
       ps)
     (vl-jp-definfo-aux (cdr defines) ifdefmap defmap))))

(define vl-jp-definfo ((defines  vl-defines-p)
                       (ifdefmap vl-ifdef-use-map-p)
                       (defmap   vl-def-use-map-p)
                       &key
                       (ps 'ps))
  (b* ((ifdefmap (make-fast-alist ifdefmap))
       (defmap   (make-fast-alist defmap))
       (ps       (vl-ps-seq
                  (vl-print "{")
                  (vl-jp-definfo-aux defines ifdefmap defmap)
                  (vl-print "}"))))
    (fast-alist-free ifdefmap)
    (fast-alist-free defmap)
    ps))



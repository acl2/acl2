; XDOC Documentation System for ACL2
; Copyright (C) 2018 Centaur Technology
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
; Original author (this file): Sol Swords <sswords@centtech.com>
; Original author (xdoc package): Jared Davis <jared@centtech.com>

(in-package "XDOC")


(include-book "prepare-topic")

(program)
(set-state-ok t)

(defxdoc archive-xdoc
  :parents (xdoc)
  :short "A means to save documentation from locally-included events."
  :long "

<p>Archive-xdoc lets you include some books or other events locally in an
encapsulate while keeping the xdoc documentation that they contain.</p>

<p>Usage:  To archive the xdoc from some events:</p>
@({
 (archive-xdoc <events>)
 })

<p>This produces an encapsulate that only locally runs the given events, so
that after running this form the events do not remain in the logical world.
However, archive-xdoc saves any new xdoc documentation created by these events,
after partially preprocessing it to remove references to definitions that might
no longer exist.  In particular, it expands forms such as @@(def ...),
@@(formals ...), etc., and evaluates @@(`...`) directives.</p>

<p>This process assumes that at the point of saving the xdoc, the definitions
referenced in these preprocessor forms exist and the @@(`...`) forms can be
evaluated.  If the documentation loaded in the archive-xdoc form references
definitions that aren't loaded, then the preprocessing will produce xdoc-errors
and leave notes behind in the documentation saying that those definitions
couldn't be found.</p>")

(defun remove-prev-topics (topics prev-topics-fal acc)
  (b* (((when (atom topics)) (reverse acc))
       (x (car topics))
       (name (cdr (assoc :name x)))
       (look (cdr (hons-get name prev-topics-fal))))
    (remove-prev-topics
     (cdr topics) prev-topics-fal
     (if (equal x look)
         acc
       (cons x acc)))))


(defun archive-preprocess-topics (topics state acc)
  (b* (((when (atom topics)) (mv (reverse acc) state))
       (x (car topics))
       (name     (cdr (assoc :name x)))
       (base-pkg (cdr (assoc :base-pkg x)))
       (short    (or (cdr (assoc :short x)) ""))
       (long     (or (cdr (assoc :long x)) ""))
       (preproc-data `((:context . ,name)
                       (:base-pkg . ,base-pkg)
                       (:archive-p . t)
                       (:kpa . ,(known-package-alist state))))
       ((mv short-acc state)
        (preprocess-aux short 0 (length short) 0 preproc-data state nil))
       (short (str::printtree->str short-acc))
       ((mv long-acc state)
        (preprocess-aux long 0 (length long) 0 preproc-data state nil))
       (long (str::printtree->str long-acc)))
    (archive-preprocess-topics
     (cdr topics) state
     (cons (replace-assoc :long long (replace-assoc :short short x))
           acc))))


(defun archive-xdoc-store (state)
  (b* ((topics (get-xdoc-table (w state)))
       (prev-topics (cdr (assoc :prev-topics (table-alist 'archive-xdoc (w state)))))
       (prev-topics-fal (topics-fal prev-topics))
       (new-topics (remove-prev-topics topics prev-topics-fal nil))
       (prev-get-event-table (and (boundp-global 'xdoc-get-event-table state)
                                  (list (@ xdoc-get-event-table))))
       (state (f-put-global 'xdoc-get-event-table
                            (make-get-event*-table (w state) nil)
                            state))
       ((mv preproc-topics state)
        (archive-preprocess-topics new-topics state nil))
       (state (if prev-get-event-table
                  (f-put-global 'xdoc-get-event-table (car prev-get-event-table) state)
                (makunbound-global 'xdoc-get-event-table state))))
    (value `(table xdoc 'doc
                   (append ',preproc-topics (get-xdoc-table world))))))

(defmacro archive-xdoc-init ()
  `(local (table archive-xdoc :prev-topics (get-xdoc-table world))))

(defun archive-xdoc-fn (events state)
  ;; This index is just to defeat redundancy of the encapsulate.
  (b* ((next-index (+ 1 (nfix (cdr (assoc :archive-xdoc-count (table-alist 'archive-xdoc (w state))))))))
    `(encapsulate nil
       (table archive-xdoc :archive-xdoc-count ,next-index)
       (archive-xdoc-init)
       (local (progn . ,events))
       (with-output :off :all :on (error)
         (make-event
          (archive-xdoc-store state))))))

(defmacro archive-xdoc (&rest events)
  `(make-event (archive-xdoc-fn ',events state)))





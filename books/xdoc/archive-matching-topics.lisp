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


(include-book "std/util/bstar" :dir :system)
(include-book "xdoc-error")
(include-book "std/strings/fast-cat" :dir :system) ;; needed to make string concatenations fast enough.
(include-book "defxdoc-raw") ;; for all-xdoc-topics
(program)

(defun remove-bound-topics (x fal acc)
  (if (atom x)
      (reverse acc)
    (remove-bound-topics
     (cdr x) fal
     (if (hons-get (cdr (assoc :name (car x))) fal)
         acc
       (cons (car x) acc)))))


(defun replace-bound-topics (x fal acc used-fal)
  (if (atom x)
      (mv (reverse acc) used-fal)
     (b* ((name (cdr (assoc :name (car x))))
          (look (hons-get name fal)))
       (if (and look
                (equal (cdr (assoc :from (car x)))
                       (cdr (assoc :from (cdr look)))))
           (replace-bound-topics
            (cdr x) fal (cons (cdr look) acc)
            (hons-acons name t used-fal))
         (replace-bound-topics
          (cdr x) fal (cons (car x) acc) used-fal)))))

(defun replace-or-add-topics (new-topics existing-topics)
  (b* ((new-topics-fal (topics-fal new-topics))
       ((mv replaced-topics used-fal) (replace-bound-topics existing-topics new-topics-fal nil nil))
       (- (fast-alist-free new-topics-fal))
       (new-new-topics (remove-bound-topics new-topics used-fal nil)))
    (fast-alist-free used-fal)
    (append new-new-topics replaced-topics)))

(defun find-var-named (name term)
  (if (atom term)
      (and (symbolp term)
           (equal (symbol-name term) name)
           term)
    (or (find-var-named name (car term))
        (and (consp (cdr term))
             (find-var-named name (cdr term))))))

(defun archive-matching-topics-fn (term)
  (b* ((x (find-var-named "X" term))
       ((unless x) (er hard? 'archive-matching-topics "Term must reference a variable named \"X\"")))
    `(encapsulate nil
       (logic)
       (set-state-ok t)
       (local (include-book "xdoc/archive" :dir :system))
       (local (defun filter-matching-topics (x state acc)
                (declare (xargs :mode :program))
                (declare (ignorable state))
                (if (atom x)
                    (reverse acc)
                  (filter-matching-topics
                   (cdr x) state
                   (let* ((,x (car x))
                          (world (w state)))
                     (declare (ignorable world))
                     (if ,term
                         (cons ,x acc)
                       acc))))))
       (comp t) ; Matt K. mod: seems necessary for Allegro CL
       (make-event
        (b* (((er all-topics) (all-xdoc-topics state))
             (topics (filter-matching-topics all-topics state nil))
             (prev-get-event-table (and (boundp-global 'xdoc-get-event-table state)
                                        (list (@ xdoc-get-event-table))))
             (state (f-put-global 'xdoc-get-event-table
                                  (make-get-event*-table (w state) nil)
                                  state))
             (- (initialize-xdoc-errors t))
             ((mv preproc-topics state)
              (archive-preprocess-topics topics state nil))
             (- (report-xdoc-errors 'archive-matching-topics))
             (state (if prev-get-event-table
                        (f-put-global 'xdoc-get-event-table (car prev-get-event-table) state)
                      (makunbound-global 'xdoc-get-event-table state))))
          (value `(table xdoc 'doc (replace-or-add-topics ',preproc-topics (get-xdoc-table world)))))))))

(defmacro archive-matching-topics (term)
  (archive-matching-topics-fn term))

(defxdoc archive-matching-topics
  :parents (xdoc)
  :short "An event that saves documentation from certain events, filtered by customizable criteria."
  :long " <p>This event has a similar purpose to that of @(see archive-xdoc).
However, instead of acting on the new xdoc topics that are created by some set
of local events, it acts on all existing topics that fit some matching
criterion.</p>

<p>Usage: @('<term>') must be a term that uses a variable named X (in any
package); it may also use @('acl2::world') and @('acl2::state').  The following
form preprocesses all existing xdoc topics for which term returns
true (non-NIL) when the topic is bound to X and the current acl2 world and
state are bound to world and state, respectively.</p>
@({
 (archive-matching-topics <term>)
 })

<p>Thus the following could be put in a book that, when included, loads all the
documentation from @('std/strings') but does not load the actual functions and
events from there:</p>

@({
 (include-book \"xdoc/archive-matching-topics\" :dir :system)
 (local (include-book \"std/strings/top\" :dir :system))

 (archive-matching-topics (str::strprefixp \"[books]/std/strings/\" (cdr (assoc :from x))))
 })

<p>The topics that are archived by this event may be ones that were process
assumes that at the point of saving the xdoc, the definitions referenced in
these preprocessor forms exist and the @@(`...`) forms can be evaluated.  If
the documentation loaded in the archive-xdoc form references definitions that
aren't loaded, then the preprocessing will produce xdoc-errors and leave notes
behind in the documentation saying that those definitions couldn't be
found.</p>")



;; (logic)

;; (local (archive-matching-topics (str::strprefixp "[books]/std/strings/" (cdr (assoc :from x)))))

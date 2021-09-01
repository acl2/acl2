; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
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

; save-fancy.lisp
;
; Writes out the XDOC database into JSON format for the new, fancy viewer.

(in-package "XDOC")
(include-book "save-classic")
(include-book "importance")
(include-book "linkcheck")
(include-book "centaur/bridge/to-json" :dir :system)
(include-book "oslib/copy" :dir :system)

(include-book "centaur/misc/tshell" :dir :system)

(set-state-ok t)
(program)

(defun-inline json-encode-string (x acc)
  (declare (type string x))
  (cons #\" (bridge::json-encode-str x (cons #\" acc))))


(defun json-encode-filename (x acc)
  (declare (type symbol x))
  (json-encode-string
   (str::rchars-to-string (file-name-mangle x nil))
   acc))

(defun json-encode-filenames-aux (x acc)
  (declare (xargs :guard (symbol-listp x)))
  (b* (((when (atom x))
        acc)
       (acc (json-encode-filename (car x) acc))
       ((when (atom (cdr x)))
        acc)
       (acc (cons #\, acc)))
    (json-encode-filenames-aux (cdr x) acc)))

(defun json-encode-filenames (x acc)
  (declare (xargs :guard (symbol-listp x)))
  (b* ((acc (cons #\[ acc))
       (acc (json-encode-filenames-aux x acc)))
    (cons #\] acc)))

#||
(str::rchars-to-string (json-encode-filename 'xdoc::foo nil))
(str::rchars-to-string (json-encode-filenames '(xdoc::a acl2::b str::c) nil))
||#

(defun json-encode-topicname (x base-pkg acc)
  (declare (type symbol x)
           (type symbol base-pkg))
  (json-encode-string
   (str::rchars-to-string (sym-mangle-cap x base-pkg nil nil))
   acc))

(defun json-encode-topicnames-aux (x base-pkg acc)
  (declare (xargs :guard (symbol-listp x)))
  (b* (((when (atom x))
        acc)
       (acc (json-encode-topicname (car x) base-pkg acc))
       ((when (atom (cdr x)))
        acc)
       (acc (cons #\, acc)))
    (json-encode-topicnames-aux (cdr x) base-pkg acc)))

(defun json-encode-topicnames (x base-pkg acc)
  (declare (xargs :guard (symbol-listp x)))
  (b* ((acc (cons #\[ acc))
       (acc (json-encode-topicnames-aux x base-pkg acc)))
    (cons #\] acc)))


#||
(str::rchars-to-string (json-encode-topicname 'xdoc::foo 'acl2::foo nil))
(str::rchars-to-string (json-encode-topicname 'xdoc::foo 'xdoc::bar nil))
(str::rchars-to-string (json-encode-topicnames '(acl2::sock-monster xdoc::shoe-monster)
                                               'xdoc::bar nil))
||#

(defun json-encode-uid (x acc)
  (declare (type integer x))
  (if (< x 0)
      (str::revappend-nat-to-dec-chars (- x) (cons #\- acc))
    (str::revappend-nat-to-dec-chars x acc)))

(defun json-encode-uids-aux (x acc)
  (declare (xargs :guard (integer-listp x)))
  (b* (((when (atom x))
        acc)
       (acc (json-encode-uid (car x) acc))
       ((when (atom (cdr x)))
        acc)
       (acc (cons #\, acc)))
    (json-encode-uids-aux (cdr x) acc)))

(defun json-encode-uids (x acc)
  (declare (xargs :guard (integer-listp x)))
  (b* ((acc (cons #\[ acc))
       (acc (json-encode-uids-aux x acc)))
    (cons #\] acc)))

#||
(str::rchars-to-string (json-encode-uids '() nil))
(str::rchars-to-string (json-encode-uids '(1 2 3) nil))
(str::rchars-to-string (json-encode-uids '(2 3 17 100) nil))
(str::rchars-to-string (json-encode-uids '(1 2 -3 -77) nil))
||#

(defun make-uid-map (n topics map)
  (b* (((when (atom topics))
        map)
       (name1 (cdr (assoc :name (car topics))))
       (map   (hons-acons name1 n map)))
    (make-uid-map (+ n 1) (cdr topics) map)))

(defun collect-uids (names uid-map)
  ;; Converts missing names into -1's.
  (b* (((when (atom names))
        nil)
       (look (cdr (hons-get (car names) uid-map)))
       ((when look)
        (cons (nfix look) (collect-uids (cdr names) uid-map))))
    (cons -1 (collect-uids (cdr names) uid-map))))


; The basic idea here is to split the database into two files:
;
;  - The INDEX will be an array containing sub-arrays with
;        [key, name, parents, short, ...]
;
;  - The DATA will bind KEY -> long
;
; Where the KEYs are just the "file names" in the old scheme.  That is, they
; are nice, safe names that can be used in URLs or wherever.
;
; Why not just save it as one big table?  The hope is that this kind of split
; will let us (in the web interface) load in the index and give the user a
; working display, even before the data has been loaded.
;
; As of July 2013, the serialized version of the xdoc table (before
; preprocessing, mind you) is 7.1 MB.  The JSON-encoded, post-preprocessing
; (i.e., proper XML) version is over 22 MB.  This doesn't count the additional
; documentation internal to Centaur or other companies.  Even with fast
; internet connections, that can be a noticeable delay, and the size will only
; grow.
;
; We previously represented the XINDEX as a hash binding KEY -> [name, ...],
; but we now use an array instead and embed the key within it.  The advantage
; of this new scheme is that it gives us an implicit way to refer to topics,
; viz., their position in the array.  This seems like a useful capability for
; implementing search features.

(defun short-xml-for-topic (topic xtopic state)
  ;; Returns (mv xml-string state)
  (b* ((short    (or (cdr (assoc :short topic)) ""))
       ;; (base-pkg (cdr (assoc :base-pkg topic)))
       (name     (cdr (assoc :name topic)))
       ((xtopic xtopic))
       ;; ((mv short-rchars state)
       ;;  (preprocess-main short name topics-fal nil base-pkg state nil))
       ;; (short-str (str::printtree->str short-rchars))
       ;; ((mv err &) (parse-xml short-str))
       (err xtopic.short-err)
       (short-str short)
       (state
        (if err
            (pprogn
             (prog2$ (note-xdoc-error) state)
; See comment regarding the use of "; xdoc error" instead of "WARNING"
; in preprocess-topic (file prepare-topic.lisp).
             (fms "~|~%; xdoc error: problem with :short in topic ~x0:~%"
                  (list (cons #\0 name))
                  *standard-co* state nil)
             (princ$ err *standard-co* state)
             (fms "~%~%" nil *standard-co* state nil))
          state))
       (short-str-xml
        (b* (((unless err)
              short-str)
             (tmp nil)
             (tmp (str::printtree-rconcat
                   "<b><color rgb='#ff0000'>Markup error in :short</color></b>
                    <code>" tmp))
             (tmp (simple-html-encode-str err 0 (length err) tmp))
             (tmp (str::printtree-rconcat "</code>" tmp)))
          (str::printtree->str tmp))))
    (mv short-str-xml state)))

(defun long-xml-for-topic (topic xtopic state)
  ;; Returns (mv xml-string state)
  (b* ((long     (or (cdr (assoc :long topic)) ""))
       ;; (base-pkg (cdr (assoc :base-pkg topic)))
       (name     (cdr (assoc :name topic)))
       ((xtopic xtopic))
       ;; ((mv long-rchars state)
       ;;  (preprocess-main long name topics-fal nil base-pkg state nil))
       ;; (long-str (str::printtree->str long-rchars))
       ;; ((mv err &) (parse-xml long-str))
       (err xtopic.long-err)
       (long-str long)
       (state
        (if err
            (pprogn
             (prog2$ (note-xdoc-error) state)
; See comment regarding the use of "; xdoc error" instead of "WARNING"
; in preprocess-topic (file prepare-topic.lisp).
             (fms "~|~%; xdoc error: problem with :long in topic ~x0:~%"
                  (list (cons #\0 name))
                  *standard-co* state nil)
             (princ$ err *standard-co* state)
             (fms "~%~%" nil *standard-co* state nil))
          state))
       (long-str-xml
        (b* (((unless err)
              long-str)
             (tmp nil)
             (tmp (str::printtree-rconcat
                   "<h3><color rgb='#ff0000'>Markup error in :long</color></h3>
                    <code>" tmp))
             (tmp (simple-html-encode-str err 0 (length err) tmp))
             (tmp (str::printtree-rconcat "</code>" tmp)))
          (str::printtree->str tmp))))
    (mv long-str-xml state)))


(defun json-encode-index-entry (topic topics xtopics-fal uid-map state acc)
  (b* ((- (check-topic-syntax topic))

       (name      (cdr (assoc :name topic)))
       (base-pkg  (cdr (assoc :base-pkg topic)))
       (parents   (cdr (assoc :parents topic)))
       (suborder0 (cdr (assoc :suborder topic)))
       (suborder-flg (suborder-indicates-chronological-p suborder0))
       (suborder  (if suborder-flg
                      (apply-suborder suborder0
                                      (find-children name topics t))
                    suborder0))

       (parent-uids (collect-uids parents uid-map))
       (suborder    (and suborder (collect-uids suborder uid-map)))
       (xtopic   (cdr (hons-get name xtopics-fal)))
       ((mv short-str state) (short-xml-for-topic topic xtopic state))

; I originally used a JSON object like {"name":"Append","rawname":"..."}  But
; then some back-of-the-napkin calculations said that these nice names were
; taking up about 400 KB of space in the index, so I figured I'd get rid of
; them and just use an array.

; IF YOU ADD/CHANGE THE ORDER THEN YOU MUST UPDATE XDOC.JS:

       ;; [key
       (acc (cons #\[ acc))
       (acc (json-encode-filename name acc))

       ; ,name (xml encoded nice topic name)
       (acc (cons #\, acc))
       (acc (json-encode-topicname name base-pkg acc))

       ; ,raw name (non-encoded symbol name, no package)
       (acc (cons #\, acc))
       (acc (json-encode-string (symbol-name name) acc))

       ; ,parent keys (array of keys for parents)
       (acc (cons #\, acc))
       (acc (json-encode-uids parent-uids acc))

       ; ,short: xml encoded short topic description
       (acc (cons #\, acc))
       (acc (json-encode-string short-str acc))

       ;; most topics don't have a suborder, so only include this if they do have one.
       (acc (b* (((unless suborder)
                  acc)
                 (acc (cons #\, acc))
                 (acc (json-encode-uids suborder acc)))
              acc))

       (acc (cons #\] acc)))
    (mv acc state)))

#||
(b* ((topics (get-xdoc-table (w state)))
     (topics-fal (topics-fal topics))
     (uid-map nil)
     ((mv acc state)
      (json-encode-index-entry topics (car topics) topics-fal uid-map state nil))
     (state (princ$ (str::rchars-to-string acc) *standard-co* state)))
  state)
||#

(defun json-encode-index-aux (all-topics topics xtopics-fal uid-map state acc)
  (b* (((when (atom topics))
        (mv acc state))
       ((mv acc state) (json-encode-index-entry (car topics) all-topics xtopics-fal
                                                uid-map state acc))
       ((when (atom (cdr topics)))
        (mv acc state))
       (acc (list* #\Space #\Newline #\, acc)))
    (json-encode-index-aux all-topics (cdr topics) xtopics-fal uid-map state acc)))

(defun json-encode-index (topics0 topics xtopics-fal uid-map state acc)

; Topics is a version of topics0 that has been ordered.  Topics0 preserves the
; order in which each topic was introduced into the xdoc table.

  (b* ((acc (cons #\[ acc))
       ((mv acc state)
        (json-encode-index-aux topics0 topics xtopics-fal uid-map state acc))
       (acc (cons #\] acc)))
    (mv acc state)))

#||
(b* ((topics     (take 5 (get-xdoc-table (w state))))
     (topics-fal (topics-fal topics))
     ((mv acc state)
      (json-encode-index topics topics topics-fal state nil))
     (state (princ$ (str::rchars-to-string acc) *standard-co* state)))
  state)
||#


(defun json-encode-data-entry (topic xtopics-fal state acc)
  (b* ((- (check-topic-syntax topic))
       (name     (cdr (assoc :name topic)))
       (base-pkg (cdr (assoc :base-pkg topic)))
       (parents  (cdr (assoc :parents topic)))
       (from     (or (cdr (assoc :from topic)) "Unknown"))

       (xtopic   (cdr (hons-get name xtopics-fal)))
       ((mv long-str state) (long-xml-for-topic topic xtopic state))

       (from-xml (str::rchars-to-string
                  (simple-html-encode-chars
                   (coerce from 'list) nil)))

       (acc (json-encode-filename name acc))
       (acc (str::revappend-chars ":[" acc))

; IF YOU ADD/CHANGE THE ORDER THEN YOU MUST UPDATE XDOC.JS:

       ; parent names (xml encoded nice parent names)
       ; BOZO move to xdata, probably
       (acc (json-encode-topicnames parents base-pkg acc))
       (acc (cons #\, acc))

       (acc (json-encode-string from-xml acc))
       (acc (cons #\, acc))

       (acc (json-encode-string (symbol-package-name base-pkg) acc))
       (acc (cons #\, acc))

       (acc (json-encode-string long-str acc))
       (acc (cons #\] acc)))
    (mv acc state)))

#||
(b* ((topics (get-xdoc-table (w state)))
     (topics-fal (topics-fal topics))
     ((mv acc state)
      (json-encode-data-entry (car topics) topics-fal state nil))
     (state (princ$ (str::rchars-to-string acc) *standard-co* state)))
  state)
||#

(defun json-encode-data-aux (topics xtopics-fal state acc)
  (b* (((when (atom topics))
        (mv acc state))
       ((mv acc state) (json-encode-data-entry (car topics) xtopics-fal state acc))
       ((when (atom (cdr topics)))
        (mv acc state))
       (acc (list* #\Space #\Newline #\Newline #\, acc)))
    (json-encode-data-aux (cdr topics) xtopics-fal state acc)))

(defun json-encode-data (topics xtopics-fal state acc)
   (b* ((acc (cons #\{ acc))
        ((mv acc state) (json-encode-data-aux topics xtopics-fal state acc))
        (acc (cons #\} acc)))
     (mv acc state)))

#||
(b* ((topics (take 5 (get-xdoc-table (w state))))
     (topics-fal (topics-fal topics))
     (acc nil)
     ((mv acc state)
      (json-encode-data topics topics-fal state acc))
     (state (princ$ (str::rchars-to-string acc) *standard-co* state)))
  state)
||#

(defun save-json-files (topics dir state)
  (b* ((topics0 (force-missing-parents
                 (maybe-add-top-topic
                  (normalize-parents-list
                   (clean-topics topics)))))

       (prev-event-table-binding
        ;; save the previous binding (or lack) of xdoc-get-event-table, set it
        ;; to one generated from the current world, and restore at the end
        (and (acl2::f-boundp-global 'xdoc-get-event-table state)
              (list (f-get-global 'xdoc-get-event-table state))))
       (state (f-put-global 'xdoc-get-event-table (make-get-event*-table (w state) nil) state))

       (topics-fal (time$ (topics-fal topics0)))

       (- (cw "; Preprocessing ~x0 topics.~%" (len topics0)))
       ((mv preproc-topics state) (time$ (preprocess-transform-topics topics0 topics-fal state)
                              :msg "; Preprocessing: ~st sec, ~sa bytes.~%"))

       (- (cw "; XML parsing preprocessed topics.~%"))
       ((mv xtopics state) (time$ (xtopics-from-topics preproc-topics state)
                                  :msg "; XML parsing: ~st sec, ~sa bytes.~%"))

       (- (cw "; Saving JSON files for ~x0 topics.~%" (len topics0)))
       ((mv ordered-topics ?sitemap state)
        (time$ (order-topics-by-importance preproc-topics xtopics state)
               :msg "; Importance sorting topics: ~st sec, ~sa bytes.~%"
               :mintime 1/2))

       ;; (smfile (oslib::catpath dir "sitemap.xml"))
       ;; ((mv channel state) (open-output-channel smfile :character state))
       ;; (state (princ$ sitemap channel state))
       ;; (state (close-output-channel channel state))

       (lcfile (oslib::catpath dir "linkcheck.html"))
       ((mv channel state) (open-output-channel lcfile :character state))
       (state (princ$ (linkcheck xtopics) channel state))
       (state (close-output-channel channel state))

;       (topics-fal (time$ (topics-fal topics)))
       (uid-map    (time$ (make-uid-map 0 ordered-topics nil)))

       (index nil)
       (index (str::revappend-chars "var xindex = " index));
       (xtopics-fal (time$ (xtopics-fal xtopics)))
       ((mv index state)
        (time$ (json-encode-index preproc-topics ordered-topics xtopics-fal uid-map state index)
               :msg "; Preparing JSON index: ~st sec, ~sa bytes.~%"))
       (index (cons #\; index))
       (index (str::rchars-to-string index))
       (idxfile (oslib::catpath dir "xindex.js"))
       ((mv channel state) (open-output-channel idxfile :character state))
       (state (princ$ index channel state))
       (state (close-output-channel channel state))

       (data nil)
       (data (str::revappend-chars "var xdata = " data))
       ((mv data state)
        (time$ (json-encode-data ordered-topics xtopics-fal state data)
               :msg "; Preparing JSON topic data: ~st sec, ~sa bytes.~%"
               :mintime 1/2))
       (data (cons #\; data))
       (data (str::rchars-to-string data))
       (datafile (oslib::catpath dir "xdata.js"))
       ((mv channel state) (open-output-channel datafile :character state))
       (state (princ$ data channel state))
       (state (close-output-channel channel state))

       (orphans (find-orphaned-topics topics topics-fal nil))


        (- (fast-alist-free (@ xdoc-get-event-table)))
        (state (if prev-event-table-binding
                   (f-put-global 'xdoc-get-event-table (car prev-event-table-binding) state)
                 (makunbound-global 'xdoc-get-event-table state))))

    (or (not orphans)
        (cw "~|~%WARNING: found topics with non-existent parents:~%~x0~%These ~
             topics may only show up in the index pages.~%~%" orphans))

    (fast-alist-free topics-fal)
    (fast-alist-free uid-map)
    state))

(defun copy-resource-dirs (resdir              ;; path to new-manual/res
                           resource-dirs-alist ;; alist created by add-resource-directory
                           state)
  (b* (((when (atom resource-dirs-alist))
        state)
       ((cons dirname source-path) (car resource-dirs-alist))
       (target-path (oslib::catpath resdir dirname))
       (- (cw ";; Copying ~s0 --> ~s1.~%" source-path target-path))
       (state       (oslib::copy! source-path target-path :recursive t)))
    (copy-resource-dirs resdir (cdr resource-dirs-alist) state)))

(defun prepare-fancy-dir (dir logo-image state)
  (b* (((unless (stringp dir))
        (er hard? 'prepare-fancy-dir "Dir must be a string, but is: ~x0.~%" dir)
        state)

       (dir-system     (acl2::f-get-global 'acl2::system-books-dir state))
       (xdoc-dir       (oslib::catpath dir-system "xdoc"))
       (xdoc/fancy     (oslib::catpath xdoc-dir "fancy"))

       (- (cw "; Preparing directory ~s0.~%" dir))
       (state (time$ (oslib::rmtree! dir)
                     :msg ";; Removing old directory: ~st sec, ~sa bytes.~%"))

       (state (time$ (oslib::copy! xdoc/fancy dir :recursive t)
                     :msg ";; Copying xdoc/fancy files: ~st sec, ~sa bytes.~%"))

       (state (if (not logo-image)
                  state
                (time$ (b* ((dir/xdoc-logo.png (oslib::catpath dir "xdoc-logo.png"))
                            ((mv error state)
                             (oslib::copy-file logo-image dir/xdoc-logo.png
                                               :overwrite t))
                            ((when error)
                             (er hard? 'prepare-fancy-dir
                                 "Error copying logo image: ~@0" error)
                             state))
                         state)
                       :msg ";; Installing custom logo: ~st sec, ~sa bytes.~%")))

       (- (cw "; Copying resource directories.~%"))
       (resdir              (oslib::catpath dir "res"))
       (resource-dirs-alist (cdr (assoc 'resource-dirs (table-alist 'xdoc (w state)))))
       (state               (time$ (copy-resource-dirs resdir resource-dirs-alist state)
                                   :msg ";; Copying resource directories: ~st sec, ~sa bytes.~%")))

    state))

(defttag :xdoc) ; for sys-call+ call below

(defun run-fancy-zip (dir state)
  (b* ((- (cw "; XDOC: Running zip.sh to create download/ directory.~%"))
       ;; We formerly used oslib::catpath here.  However, David Rager reported
       ;; (2014-06-24) that this caused failures when using directories such as
       ;; "~/public_html", because the ~ doesn't get wildcard expanded in all
       ;; Lisps, e.g., CCL.  So, we now use ACL2's extend-pathname, since it
       ;; gets rid of the ~ characters.
       (dir-fix (acl2::extend-pathname dir "." state))
       (zip.sh  (acl2::extend-pathname dir-fix "zip.sh" state))
       (cmd (string-append "sh "
             (string-append zip.sh
              (string-append " " dir-fix))))
       ((mv exit-status lines)
        (time$ (acl2::tshell-call cmd :print t)
               :msg "; XDOC zip.sh: ~st sec, ~sa bytes.~%"))
       ((unless (equal exit-status 0))
        (acl2::warning$ 'run-fancy-zip "run-fancy-zip"
                        "zip.sh failed to create a zip file for directory ~x0 ~
                         (exit code ~x1).  ~x2."
                        dir-fix exit-status lines)))
    state))

; The check done by check-xdoc-topics (and addition of functions below to
; support it) was added by Matt K. in November 2019, to ease debugging of the
; case that a non-standard character in the :long string can cause there to be
; an empty page in the web-based manual.  (This actually happened when a stray
; control-P wound up in the documentation for defstobj.)  Note that this check
; is probably not complete, for example since preprocessing has not yet been
; applied to the given topics.  Rather than try to get a clearer understanding
; of the generation of web pages from xdoc source, I'm taking this conservative
; approach.  Our first implementation did not allow tabs, but that uncovered 23
; violations in the acl2+books manual, so for now at least we'll allow tabs.

(defun standard+-string-p1 (x n)
; Based on standard-string-p1 in the ACL2 source code.
  (declare (xargs :guard (and (stringp x)
                              (natp n)
                              (<= n (length x)))))
  (cond ((zp n) t)
        (t (let ((n (1- n)))
             (and (or (standard-char-p (char x n))
                      (eql (char x n) #\Tab))
                  (standard+-string-p1 x n))))))

(defun standard+-string-p (x)
  (declare (xargs :guard (stringp x)))
  (standard+-string-p1 x (length x)))

(defun non-standard+-char-position1 (x n)
; Based on standard-string-p1 in the ACL2 source code.
  (declare (xargs :guard (and (stringp x)
                              (natp n)
                              (<= n (length x)))))
  (cond ((zp n) nil)
        (t (let ((n (1- n)))
             (if (or (standard-char-p (char x n))
                     (eql x #\Tab))
                 (non-standard+-char-position1 x n)
               n)))))

(defun non-standard+-char-position (x)
  (declare (xargs :guard (stringp x)))
  (non-standard+-char-position1 x (length x)))

(defun check-xdoc-topics (topics msg-list)
  (cond
   ((endp topics)
    (cond
     (msg-list (er hard 'check-xdoc-topics
                   "~|~%~*0"
                   `("impossible"             ; when nothing to print
                     "~@*."                   ; the last element
                     "~@*; and~|~%"           ; the 2nd to last element
                     "~@*;~|~%"               ; all other elements
                     ,msg-list)))
     (t nil)))
   (t
    (check-xdoc-topics
     (cdr topics)
     (let* ((topic (car topics))
            (ap (alistp (car topics)))
            (short (and ap (cdr (assoc-eq :short topic))))
            (long (and ap (cdr (assoc-eq :long topic)))))
       (cond
        ((not ap) ; impossible?
         (cons (msg "Topic is not an alist: ~x0"
                    topic)
               msg-list))
        (t
         (let* ((msg-list
                 (cond
                  ((and short
                        (not (standard+-string-p short)))
                   (let ((posn (non-standard+-char-position short)))
                     (cons (msg "Found non-standard character, ~x0, in the ~
                                 :short string of the topic named ~x1, at ~
                                 position ~x2"
                                (char short posn)
                                (cdr (assoc-eq :name topic))
                                posn)
                           msg-list)))
                  (t msg-list)))
                (msg-list
                 (cond
                  ((and long
                        (not (standard+-string-p long)))
                   (let ((posn (non-standard+-char-position long)))
                     (cons (msg "Found non-standard character, ~x0, in the ~
                                 :long string of the topic named ~x1, at ~
                                 position ~x2"
                                (char long posn)
                                (cdr (assoc-eq :name topic))
                                posn)
                           msg-list)))
                  (t msg-list))))
           msg-list))))))))

(defun save-fancy (all-topics dir zip-p logo-image broken-links-limit state)
  (prog2$
   (check-xdoc-topics all-topics nil)
   (b* ((state (f-put-global 'broken-links-limit broken-links-limit state))
        (state (prepare-fancy-dir dir logo-image state))
        (state (save-json-files all-topics dir state))
        (state (if zip-p
                   (run-fancy-zip dir state)
                 state)))
     state)))

; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
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
   (str::rchars-to-string (sym-mangle-cap x base-pkg nil))
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
      (str::revappend-natchars (- x) (cons #\- acc))
    (str::revappend-natchars x acc)))

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

(defun short-xml-for-topic (topic topics-fal state)
  ;; Returns (mv xml-string state)
  (b* ((short    (or (cdr (assoc :short topic)) ""))
       (base-pkg (cdr (assoc :base-pkg topic)))
       (name     (cdr (assoc :name topic)))
       ((mv short-rchars state) (preprocess-main short name topics-fal base-pkg state nil))
       (short-str (str::rchars-to-string short-rchars))
       ((mv err &) (parse-xml short-str))
       (state
        (if err
            (pprogn
               (fms "~|~%WARNING: problem with :short in topic ~x0:~%"
                    (list (cons #\0 name))
                    *standard-co* state nil)
               (princ$ err *standard-co* state)
               (fms "~%~%" nil *standard-co* state nil))
          state))
       (short-str-xml
        (b* (((unless err)
              short-str)
             (tmp nil)
             (tmp (str::revappend-chars
                   "<b><color rgb='#ff0000'>Markup error in :short</color></b>
                    <code>" tmp))
             (tmp (simple-html-encode-str err 0 (length err) tmp))
             (tmp (str::revappend-chars "</code>" tmp)))
          (str::rchars-to-string tmp))))
    (mv short-str-xml state)))

(defun long-xml-for-topic (topic topics-fal state)
  ;; Returns (mv xml-string state)
  (b* ((long     (or (cdr (assoc :long topic)) ""))
       (base-pkg (cdr (assoc :base-pkg topic)))
       (name     (cdr (assoc :name topic)))
       ((mv long-rchars state) (preprocess-main long name topics-fal base-pkg state nil))
       (long-str (str::rchars-to-string long-rchars))
       ((mv err &) (parse-xml long-str))
       (state
        (if err
            (pprogn
               (fms "~|~%WARNING: problem with :long in topic ~x0:~%"
                    (list (cons #\0 name))
                    *standard-co* state nil)
               (princ$ err *standard-co* state)
               (fms "~%~%" nil *standard-co* state nil))
          state))
       (long-str-xml
        (b* (((unless err)
              long-str)
             (tmp nil)
             (tmp (str::revappend-chars
                   "<h3><color rgb='#ff0000'>Markup error in :long</color></h3>
                    <code>" tmp))
             (tmp (simple-html-encode-str err 0 (length err) tmp))
             (tmp (str::revappend-chars "</code>" tmp)))
          (str::rchars-to-string tmp))))
    (mv long-str-xml state)))


(defun json-encode-index-entry (topic topics-fal uid-map state acc)
  (b* ((- (check-topic-syntax topic))

       (name     (cdr (assoc :name topic)))
       (base-pkg (cdr (assoc :base-pkg topic)))
       (parents  (cdr (assoc :parents topic)))
       (suborder (cdr (assoc :suborder topic)))

       (parent-uids (collect-uids parents uid-map))
       (suborder    (and suborder (collect-uids suborder uid-map)))

       ((mv short-str state) (short-xml-for-topic topic topics-fal state))

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
      (json-encode-index-entry (car topics) topics-fal uid-map state nil))
     (state (princ$ (str::rchars-to-string acc) *standard-co* state)))
  state)
||#

(defun json-encode-index-aux (topics topics-fal uid-map state acc)
  (b* (((when (atom topics))
        (mv acc state))
       ((mv acc state) (json-encode-index-entry (car topics) topics-fal uid-map
                                                state acc))
       ((when (atom (cdr topics)))
        (mv acc state))
       (acc (list* #\Space #\Newline #\, acc)))
    (json-encode-index-aux (cdr topics) topics-fal uid-map state acc)))

(defun json-encode-index (topics topics-fal uid-map state acc)
  (b* ((acc (cons #\[ acc))
       ((mv acc state) (json-encode-index-aux topics topics-fal uid-map state acc))
       (acc (cons #\] acc)))
    (mv acc state)))

#||
(b* ((topics     (take 5 (get-xdoc-table (w state))))
     (topics-fal (topics-fal topics))
     ((mv acc state)
      (json-encode-index topics topics-fal state nil))
     (state (princ$ (str::rchars-to-string acc) *standard-co* state)))
  state)
||#


(defun json-encode-data-entry (topic topics-fal state acc)
  (b* ((- (check-topic-syntax topic))
       (name     (cdr (assoc :name topic)))
       (base-pkg (cdr (assoc :base-pkg topic)))
       (parents  (cdr (assoc :parents topic)))
       (from     (or (cdr (assoc :from topic)) "Unknown"))

       ((mv long-str state) (long-xml-for-topic topic topics-fal state))

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

(defun json-encode-data-aux (topics topics-fal state acc)
  (b* (((when (atom topics))
        (mv acc state))
       ((mv acc state) (json-encode-data-entry (car topics) topics-fal state acc))
       ((when (atom (cdr topics)))
        (mv acc state))
       (acc (list* #\Space #\Newline #\Newline #\, acc)))
    (json-encode-data-aux (cdr topics) topics-fal state acc)))

(defun json-encode-data (topics topics-fal state acc)
  (b* ((acc (cons #\{ acc))
       ((mv acc state) (json-encode-data-aux topics topics-fal state acc))
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
  (b* ((topics (force-root-parents
                (maybe-add-top-topic
                 (normalize-parents-list
                  (clean-topics topics)))))

       (- (cw "; Saving JSON files for ~x0 topics.~%" (len topics)))
       ((mv topics xtopics ?sitemap state)
        (time$ (order-topics-by-importance topics state)
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

       (topics-fal (time$ (topics-fal topics)))
       (uid-map    (time$ (make-uid-map 0 topics nil)))

       (index nil)
       (index (str::revappend-chars "var xindex = " index));
       ((mv index state)
        (time$ (json-encode-index topics topics-fal uid-map state index)
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
        (time$ (json-encode-data topics topics-fal state data)
               :msg "; Preparing JSON topic data: ~st sec, ~sa bytes.~%"
               :mintime 1/2))
       (data (cons #\; data))
       (data (str::rchars-to-string data))
       (datafile (oslib::catpath dir "xdata.js"))
       ((mv channel state) (open-output-channel datafile :character state))
       (state (princ$ data channel state))
       (state (close-output-channel channel state))

       (orphans (find-orphaned-topics topics topics-fal nil)))

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

(defun prepare-fancy-dir (dir state)
  (b* (((unless (stringp dir))
        (prog2$ (er hard? 'prepare-fancy-dir
                    "Dir must be a string, but is: ~x0.~%" dir)
                state))

       (dir-system     (acl2::f-get-global 'acl2::system-books-dir state))
       (xdoc-dir       (oslib::catpath dir-system "xdoc"))
       (xdoc/fancy     (oslib::catpath xdoc-dir "fancy"))

       (- (cw "; Preparing directory ~s0.~%" dir))
       (state          (time$ (oslib::rmtree! dir)
                              :msg ";; Removing old directory: ~st sec, ~sa bytes.~%"))

       (state          (time$ (oslib::copy! xdoc/fancy dir :recursive t)
                              :msg ";; Copying xdoc/fancy files: ~st sec, ~sa bytes.~%"))

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
        (er hard? 'run-fancy-zip
            "zip.sh failed (exit code ~x0).  ~x1."
            exit-status lines)
        state))
    state))

(defun save-fancy (all-topics dir zip-p state)
  (b* ((state (prepare-fancy-dir dir state))
       (state (save-json-files all-topics dir state))
       (state (if zip-p
                  (run-fancy-zip dir state)
                state)))
    state))

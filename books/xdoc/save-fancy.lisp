; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
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

; save-fancy.lisp
;
; Writes out the XDOC database into JSON format for the new, fancy viewer.

(in-package "XDOC")
(include-book "save-classic")
(include-book "importance")
(include-book "linkcheck")
(include-book "centaur/bridge/to-json" :dir :system)
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

(defun json-encode-index-entry (topic topics-fal uid-map state acc)
  (b* ((name     (cdr (assoc :name topic)))
       (base-pkg (cdr (assoc :base-pkg topic)))
       (short    (or (cdr (assoc :short topic)) ""))
       (long     (or (cdr (assoc :long topic)) ""))
       (parents  (cdr (assoc :parents topic)))
       ((unless (symbolp name))
        (mv (er hard? 'preprocess-topic "Name is not a string: ~x0.~%" topic)
            state))
       ((unless (symbolp base-pkg))
        (mv (er hard? 'preprocess-topic "Base-pkg is not a symbol: ~x0.~%" topic)
            state))
       ((unless (symbol-listp parents))
        (mv (er hard? 'preprocess-topic "Parents are not a symbol-listp: ~x0.~%" topic)
            state))
       ((unless (stringp short))
        (mv (er hard? 'preprocess-topic "Short is not a string: ~x0.~%" topic)
            state))
       ((unless (stringp long))
        (mv (er hard? 'preprocess-topic "Long is not a string: ~x0.~%" topic)
            state))

       (parent-uids (collect-uids parents uid-map))

       ((mv short-rchars state) (preprocess-main short nil topics-fal base-pkg state nil))
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

       (short-str
        (b* (((unless err)
              short-str)
             (tmp nil)
             (tmp (str::revappend-chars
                   "<b><color rgb='#ff0000'>Markup error in :short</color></b>
                    <code>" tmp))
             (tmp (simple-html-encode-str err 0 (length err) tmp))
             (tmp (str::revappend-chars "</code>" tmp)))
          (str::rchars-to-string tmp)))

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

       (acc (cons #\] acc)))
    (mv acc state)))

#||
(b* ((topics (get-xdoc-table (w state)))
     (topics-fal (topics-fal topics))
     ((mv acc state)
      (json-encode-index-entry (car topics) topics-fal state nil))
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
  (b* ((__function__ 'json-encode-data-entry)
       (name     (cdr (assoc :name topic)))
       (base-pkg (cdr (assoc :base-pkg topic)))
       (short    (or (cdr (assoc :short topic)) ""))
       (long     (or (cdr (assoc :long topic)) ""))
       (parents  (cdr (assoc :parents topic)))
       (from     (or (cdr (assoc :from topic)) "Unknown"))
       ((unless (symbolp name))
        (mv (er hard? __function__ "Name is not a string: ~x0.~%" topic)
            state))
       ((unless (symbolp base-pkg))
        (mv (er hard? __function__ "Base-pkg is not a symbol: ~x0.~%" topic)
            state))
       ((unless (symbol-listp parents))
        (mv (er hard? __function__ "Parents are not a symbol-listp: ~x0.~%" topic)
            state))
       ((unless (stringp short))
        (mv (er hard? __function__ "Short is not a string: ~x0.~%" topic)
            state))
       ((unless (stringp long))
        (mv (er hard? __function__ "Long is not a string: ~x0.~%" topic)
            state))
       ((unless (stringp from))
        (mv (er hard? __function__ "From is not a string: ~x0.~%" topic)
            state))

       ((mv long-rchars state) (preprocess-main long nil topics-fal base-pkg state nil))
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
       (long-str
        (b* (((unless err)
              long-str)
             (tmp nil)
             (tmp (str::revappend-chars
                   "<h3><color rgb='#ff0000'>Markup error in :long</color></h3>
                    <code>" tmp))
             (tmp (simple-html-encode-str err 0 (length err) tmp))
             (tmp (str::revappend-chars "</code>" tmp)))
          (str::rchars-to-string tmp)))

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
       ((mv topics xtopics state)
        (time$ (order-topics-by-importance topics state)
               :msg "; Importance sorting topics: ~st sec, ~sa bytes.~%"
               :mintime 1/2))

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


(defun prepare-fancy-dir (dir state)
  (b* (((unless (stringp dir))
        (prog2$ (er hard? 'prepare-fancy-dir
                    "Dir must be a string, but is: ~x0.~%" dir)
                state))
       (- (cw "; Preparing directory ~s0.~%" dir))

       (dir/lib        (oslib::catpath dir "lib"))
       (dir/images     (oslib::catpath dir "images"))
       (state          (oslib::mkdir! dir))
       (state          (oslib::mkdir! dir/lib))
       (state          (oslib::mkdir! dir/images))

       (dir-system     (acl2::f-get-global 'acl2::system-books-dir state))
       (xdoc-dir       (oslib::catpath dir-system "xdoc"))
       (xdoc/classic   (oslib::catpath xdoc-dir "classic"))
       (xdoc/fancy     (oslib::catpath xdoc-dir "fancy"))
       (xdoc/fancy/lib (oslib::catpath xdoc/fancy "lib"))

       (- (cw "Copying fancy viewer main files...~%"))
       (state          (stupid-copy-files xdoc/fancy
                                          (list "collapse_subtopics.png"
                                                "download.png"
                                                "expand_subtopics.png"
                                                "favicon.png"
                                                "Icon_External_Link.png"
                                                "index.html"
                                                "xdoc-home.png"
                                                "xdoc-logo.png"
                                                "leaf.png"
                                                "LICENSE"
                                                "minus.png"
                                                "plus.png"
                                                "print.css"
                                                "print.html"
                                                "printer.png"
                                                "render.js"
                                                "style.css"
                                                "view_flat.png"
                                                "view_tree.png"
                                                "config.js"
                                                "xdoc.js"
                                                "xslt.js"
                                                "xdoc_index.js"
                                                "xdataget.pl"
                                                "xdata2sql.pl"
                                                "zip.sh"
                                                )
                                          dir state))

       (- (cw "Copying fancy viewer library files...~%"))
       (state          (stupid-copy-files xdoc/fancy/lib
                                          (list "hogan-2.0.0.js"
                                                "jquery-2.0.3.js"
                                                "jquery-2.0.3.min.js"
                                                "jquery.base64.js"
                                                "jquery.powertip.css"
                                                "jquery.powertip.js"
                                                "jquery.powertip.min.js"
                                                "lazyload.js"
                                                "typeahead.js"
                                                "typeahead.min.js")
                                          dir/lib state))

       (- (cw "Copying ACL2 tour graphics...~%"))
       (state          (stupid-copy-files xdoc/classic
                                          *acl2-graphics*
                                          dir/images state)))
    state))


(defun run-fancy-zip (dir state)
  (b* ((- (cw "; XDOC: Running zip.sh to create download/ directory.~%"))
       ((mv erp val state)
        (time$ (sys-call+ "sh" (list (oslib::catpath dir "zip.sh") dir) state)
               :msg "; XDOC zip.sh: ~st sec, ~sa bytes.~%"))
       ((when erp)
        (er hard? 'run-fancy-zip
            "zip.sh failed (exit code ~x0).  ~x1."
            erp val)
        state))
    state))

(defun save-fancy (all-topics dir state)
  (b* ((state (prepare-fancy-dir dir state))
       (state (save-json-files all-topics dir state))
       (state (run-fancy-zip dir state)))
    state))


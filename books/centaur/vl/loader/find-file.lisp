; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "VL")
(include-book "../util/warnings")
(include-book "oslib/ls-logic" :dir :system)
(local (include-book "std/io/base" :dir :system))
(local (include-book "../util/arithmetic"))
(include-book "std/testing/assert" :dir :system)
(local (std::add-default-post-define-hook :fix))
(set-state-ok t)

(local (xdoc::set-default-parents vl-find-file))

(define vl-ends-with-directory-separatorp ((x stringp))
  :returns (bool booleanp :rule-classes :type-prescription)
  (let ((x (string-fix x))
        (len (length x)))
    (and (/= len 0)
         (eql (char x (- (length x) 1)) ACL2::*directory-separator*))))

(define vl-extend-pathname ((dir stringp) (filename stringp))
  :returns (dir/filename stringp :rule-classes :type-prescription)
  :short "@(call vl-extend-pathname) concatenates @('dir') and @('filename'),
  adding a slash to between them only if @('dir') does not end with a slash."
  (cat dir
       (if (vl-ends-with-directory-separatorp dir)
           ""
         (implode (list ACL2::*directory-separator*)))
       filename))



; Directory Caches ------------------------------------------------------------
;
; I found that just finding files was taking a long time.  So, rather than
; repeatedly hitting the filesystem, we gather up directory listings and use
; them as a cache.

(fty::defalist vl-dircache
  :key-type stringp
  :val-type acl2::any-p
  :short "Fast alist mapping file names to T."
  :long "<p>This is a cache for speeding up direct file name lookups by
  avoiding repeated filesystem access.  It is suitable for @('`include') files
  where we know the entire filename.</p>")

(fty::defalist vl-dirlist-cache
  :key-type stringp
  :val-type vl-dircache
  :short "Slow alist mapping directories names to their @(see vl-dircache)s.")

(define vl-make-dircache-aux ((files string-listp))
  :returns (cache vl-dircache-p)
  :parents (vl-make-dircache)
  (if (atom files)
      nil
    (cons (cons (hons-copy (string-fix (car files))) t)
          (vl-make-dircache-aux (cdr files)))))

(define vl-make-dircache
  :parents (vl-dircache)
  :short "Make a @(see vl-dircache) for a directory."
  ((dir      stringp          "Directory to list.")
   (warnings vl-warninglist-p "Warnings to extend in case of file errors.")
   state)
  :returns (mv (cache    vl-dircache-p)
               (warnings vl-warninglist-p)
               (state state-p1 :hyp (force (state-p1 state))))
  (b* ((dir (string-fix dir))
       ((mv err files state)
        (time$ (oslib::ls-files dir)
               :msg ";; vl-make-dircache: ls-files: ~st sec, ~sa bytes~%"
               :mintime 1/2))
       ((when err)
        (mv nil
            (warn :type :vl-filesystem-error
                  :msg "Error creating directory cache for ~s0. ~@1."
                  :args (list dir err))
            state))
       (cache (make-fast-alist (vl-make-dircache-aux files))))
    (mv cache (ok) state)))

(define vl-make-dirlist-cache
  :parents (vl-dirlist-cache)
  :short "Make a @(see vl-dirlist-cache) for a list of directories."
  ((dirs     string-listp     "Directories to list.")
   (warnings vl-warninglist-p "Warnings to extend in case of file errors.")
   state)
  :returns (mv (cache vl-dirlist-cache-p)
               (warnings vl-warninglist-p)
               (state state-p1 :hyp (force (state-p1 state))))
  ;; NOTE: importantly this keeps the directories in order.
  (b* (((when (atom dirs))
        (mv nil (ok) state))
       ((mv cache1 warnings state)
        (vl-make-dircache (car dirs) warnings state))
       ((mv rest warnings state)
        (vl-make-dirlist-cache (cdr dirs) warnings state)))
    (mv (cons (cons (hons-copy (string-fix (car dirs))) cache1)
              rest)
        warnings state))
  ///
  (defret alist-keys-of-vl-make-dirlist-cache
    ;; Proof that it keeps the directories in order.
    (equal (alist-keys cache)
           (string-list-fix dirs))))

(define vl-free-dirlist-cache ((x vl-dirlist-cache-p))
  :parents (vl-dirlist-cache)
  :short "Free the fast alist for each individual directory."
  (if (atom x)
      nil
    (progn$ (fast-alist-free (cdar x))
            (vl-free-dirlist-cache (cdr x)))))


; File Searching across Directories -------------------------------------------
;
; These "slow" functions used to be all that we did.  But even after directory
; caches, we still need these slow functions in case we are given a path to
; include that isn't simple, e.g., if you want to include the file "../foo.v",
; then that's not something our directory caches will help us find.

(define vl-file-exists-p ((filename stringp)
                          state)
  :returns (mv (exists-p booleanp :rule-classes :type-prescription)
               (state    state-p1 :hyp (force (state-p1 state))))
  (b* ((filename (string-fix filename))
       ((mv channel state)
        (open-input-channel filename :character state))
       ((unless channel)
        (mv nil state))
       (state (close-input-channel channel state)))
    (mv t state)))

(define vl-slow-find-file-aux ((filename    stringp)
                               (searchcache vl-dirlist-cache-p)
                               state)
  :short "Look for a file in a list of search directories (without using the cache)."
  :returns (mv (foundpath maybe-stringp :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :measure (len (vl-dirlist-cache-fix searchcache))
  (b* ((searchcache (vl-dirlist-cache-fix searchcache))
       ((when (atom searchcache))
        (mv nil state))
       ((cons dir ?cache) (car searchcache))
       (attempt (vl-extend-pathname dir filename))
       ((mv exists-p state)
        (time$ (vl-file-exists-p attempt state)
               :mintime 1/10
               :msg ";; vl-slow-find-file-aux file-exists-p: ~st sec, ~sa bytes for ~f0~%"
               :args (list attempt)))
       ((when exists-p)
        (mv attempt state)))
    (vl-slow-find-file-aux filename (cdr searchcache) state)))

(define vl-cache-find-file-aux
  :short "Alternative to @(see vl-slow-find-file-aux) using a @(see vl-dirlist-cache-p)."
  ((filename    stringp)
   (searchcache vl-dirlist-cache-p))
  :returns (realpath maybe-stringp :rule-classes :type-prescription)
  :measure (len (vl-dirlist-cache-fix searchcache))
  (b* ((filename    (string-fix filename))
       (searchcache (vl-dirlist-cache-fix searchcache))
       ((when (atom searchcache))
        nil)
       ((cons dir file-fal) (car searchcache))
       (exists-p (hons-get filename file-fal))
       ((when exists-p)
        (vl-extend-pathname dir filename)))
    (vl-cache-find-file-aux filename (cdr searchcache))))

(define vl-find-file
  :parents (loader)
  :short "Determine where to load a file from, given its (absolute or relative)
  name and a list of directories to search."
  ((filename    stringp            "Absolute or relative name of the file you want to load.")
   (searchcache vl-dirlist-cache-p "Directories to search, with cached file lists.")
   state)
  :returns
  (mv (realpath maybe-stringp :rule-classes :type-prescription
                "On success, the full @('dirname/filename') path to the first
                 found file.  Otherwise NIL to indicate that no such file is
                 found in any of these directories.")
      (state state-p1 :hyp (force (state-p1 state))))
  :guard-hints(("Goal" :in-theory (enable state-p1 get-global put-global)))
  (b* ((filename (string-fix filename))
       ((when (ACL2::absolute-pathname-string-p filename nil (ACL2::os (w state))))
        (mv filename state))
       ((when (or (str::substrp "/" filename)
                  (str::substrp "\\" filename)))
        ;; This looks like a complex relative filename, i.e., it might be something
        ;; like "../foo.v".  We still want to support this, but it's reaching outside
        ;; of our cache, so we'll need to do a slow lookup.
        (vl-slow-find-file-aux filename searchcache state)))
    ;; Otherwise, this is a imple filename with no directory separators, so
    ;; try to find it in our cache, instead.  We don't have to touch the
    ;; state for this.
    (mv (vl-cache-find-file-aux filename searchcache) state)))


; Searching with Extension Lists ----------------------------------------------
;
; For finding library files we need to search for files with different
; extensions, e.g., foo.v or foo.sv.  For this we use a slightly different
; cache structure.

(local (xdoc::set-default-parents vl-find-basename/extension))

(fty::defalist vl-dirxcache
  :key-type stringp
  :val-type string-listp
  :short "Fast alist mapping file prefixes to lists of extensions."
  :long "<p>This is a cache for speeding up library file finds in the search
  path.  If this directory contains files @('foo.v') and @('foo.sv'), the cache
  will map the prefix @('foo') to the list of these extensions.</p>")

(fty::defalist vl-dirxlist-cache
  :key-type stringp
  :val-type vl-dirxcache
  :short "Slow alist mapping directories names to their @(see vl-dirxcache)s.")

(define vl-split-filename ((filename stringp "E.g., @('foo.txt')."))
  :returns (mv (basename stringp :rule-classes :type-prescription
                         "E.g., @('foo').")
               (extension maybe-stringp :rule-classes :type-prescription
                          "E.g. @('txt'), or @('nil') when there is no extension."))
  :short "Split a filename into its basename and extension."
  (b* ((filename (string-fix filename))
       (pos (str::strrpos "." filename))
       ((unless pos)
        (mv filename nil))
       (basename (subseq filename 0 pos))
       (extension (subseq filename (+ 1 pos) nil)))
    (mv basename extension))
  ///
  (assert! (b* (((mv base ext) (vl-split-filename "foo.txt")))
             (and (equal base "foo")
                  (equal ext "txt"))))
  (assert! (b* (((mv base ext) (vl-split-filename "hello")))
             (and (equal base "hello")
                  (equal ext nil)))))

(define vl-make-dirxcache-aux
  ((files      string-listp "Files in the directory.")
   (extensions string-listp "Extensions we care about, e.g., @('\"v\" \"sv\"'), no dots.")
   (cache      vl-dirxcache-p "Cache we are building."))
  :returns (cache vl-dirxcache-p)
  :parents (vl-make-dirxcache)
  (b* ((cache      (vl-dirxcache-fix cache))
       (extensions (string-list-fix extensions))
       ((when (atom files))
        (vl-dirxcache-fix cache))
       ((mv basename extension)
        (vl-split-filename (car files)))
       ((unless (and extension (member-equal extension extensions)))
        ;; Not an extension we care about, don't put it in the cache.
        (vl-make-dirxcache-aux (cdr files) extensions cache))
       ;; Add this extension
       (basename  (hons-copy basename))
       (prev-exts (cdr (hons-get basename cache)))
       (cache     (hons-acons basename (cons extension prev-exts) cache)))
    (vl-make-dirxcache-aux (cdr files) extensions cache)))

(define vl-make-dirxcache
  :parents (vl-dirxcache)
  :short "Make a @(see vl-dirxcache) for a directory."
  ((dir        stringp          "Directory to list.")
   (extensions string-listp     "Extensions we care about, e.g., @('\"v\" \"sv\"'), no dots.")
   (warnings   vl-warninglist-p "Warnings to extend in case of file errors.")
   state)
  :returns (mv (cache    vl-dirxcache-p)
               (warnings vl-warninglist-p)
               (state state-p1 :hyp (force (state-p1 state))))
  (b* ((dir (string-fix dir))
       ((mv err files state)
        (time$ (oslib::ls-files dir)
               :msg "vl-make-dirxcache: ls-files: ~st sec, ~sa bytes~%"
               :mintime 1/2))
       ((when err)
        (mv nil
            (warn :type :vl-filesystem-error
                  :msg "Error creating directory cache for ~s0. ~@1."
                  :args (list dir err))
            state))
       (cache (vl-make-dirxcache-aux files extensions nil)))
    (mv cache (ok) state)))

(define vl-make-dirxlist-cache
  :parents (vl-dirxlist-cache)
  :short "Make a @(see vl-dirxlist-cache) for a list of directories."
  ((dirs       string-listp     "Directories to list.")
   (extensions string-listp     "Extensions we care about, e.g., @('\"v\" \"sv\"'), no dots.")
   (warnings   vl-warninglist-p "Warnings to extend in case of file errors.")
   state)
  :returns (mv (cache vl-dirxlist-cache-p)
               (warnings vl-warninglist-p)
               (state state-p1 :hyp (force (state-p1 state))))
  ;; NOTE: importantly this keeps the directories in order.
  (b* (((when (atom dirs))
        (mv nil (ok) state))
       ((mv cache1 warnings state)
        (vl-make-dirxcache (car dirs) extensions warnings state))
       ((mv rest warnings state)
        (vl-make-dirxlist-cache (cdr dirs) extensions warnings state)))
    (mv (cons (cons (hons-copy (string-fix (car dirs))) cache1)
              rest)
        warnings state))
  ///
  (defret alist-keys-of-vl-make-dirxlist-cache
    ;; Proof that it keeps the directories in order.
    (equal (alist-keys cache)
           (string-list-fix dirs))))

(define vl-free-dirxlist-cache ((x vl-dirxlist-cache-p))
  :parents (vl-dirxlist-cache)
  :short "Free the fast alist for each individual directory."
  (if (atom x)
      nil
    (progn$ (fast-alist-free (cdar x))
            (vl-free-dirxlist-cache (cdr x)))))


;; I don't think we actually need a slow version of this.  We need it for
;; include-dirs because when someone writes `include "foo/bar.v", we need to be
;; smart enough to not go looking for a file named 'foo/bar.v' in individual
;; directories.  But for the search path, we know something like, "we're
;; missing a definition for module 'foo'," and we want to go look for a file
;; named 'foo.v'.  It seems more reasonable *not* to try to interpret the
;; module name as possibly having directory structure.  So forget this, and
;; let's just use our cache!

;; (define vl-slow-find-basename/extension-aux
;;   :short "Search for a filename with any of a list of extensions. Slow,
;;           cache-free version."
;;   ((filename   stringp        "Base filename to search for.")
;;    (extensions string-listp   "Possible extensions to add to it.")
;;    (dir        stringp        "Directory to search in.")
;;    state)
;;   :returns (mv (hits string-listp
;;                      "Fully resolved @('dirname/filename.ext') paths for matching files.")
;;                (state state-p1 :hyp (state-p1 state)))
;;   (b* (((when (atom extensions))
;;         (mv nil state))
;;        ((mv rest state)
;;         (vl-slow-find-basename/extension-aux filename (cdr extensions) dir state))
;;        (filename1 (cat filename "." (car extensions)))
;;        (attempt (vl-extend-pathname dir filename1))
;;        ((mv exists-p state)
;;         (vl-file-exists-p attempt state)))
;;     (if exists-p
;;         (mv (cons attempt rest) state)
;;       (mv rest state))))

(define vl-find-highest-priority-extension
  ((extensions string-listp "Extensions we care about in priority order.")
   (found      string-listp "Extensions we found for this particular file."))
  :returns (hit stringp :rule-classes :type-prescription)
  :measure (len extensions)
  (b* ((extensions (string-list-fix extensions))
       (found      (string-list-fix found))
       ((when (atom extensions))
        (raise "Programming error, failed to find extension.")
        "")
       ((when (member-equal (car extensions) found))
        (car extensions)))
    (vl-find-highest-priority-extension (cdr extensions) found)))

(define vl-find-basename/extension-aux
  :short "Search for a filename with any of a list of extensions."
  ((filename   stringp          "Base filename to search for.")
   (extensions string-listp     "Possible extensions to add to it.")
   (dir        stringp          "Directory to search in.")
   (dirxcache  vl-dirxcache-p   "Cache for this directory and extensions.")
   (warnings   vl-warninglist-p "Warnings accumulator."))
  :returns (mv (realfile maybe-stringp
                         "In case of a match, the full @('dirname/filename.ext')
                          path to load.  Otherwise @('nil').")
               (warnings vl-warninglist-p
                         "Possibly extended with ambiguity warnings."))
  (b* ((filename   (string-fix filename))
       (dir        (string-fix dir))
       (dirxcache  (vl-dirxcache-fix dirxcache))
       (found-exts (cdr (hons-get filename dirxcache)))
       ((when (atom found-exts))
        ;; No files matching filename.ext are found in this directory for any
        ;; ext that we care about.  We fail.  But that's fine and nothing to
        ;; warn about; maybe it's in another directory.
        (mv nil (ok)))
       ;; Found at least one filename.ext that matches.  Hopefully there is
       ;; only one.  If not, choose in priority order and also issue a warning.
       (winner (if (atom (cdr found-exts))
                   (first found-exts)
                 (vl-find-highest-priority-extension extensions found-exts)))
       (realfile (vl-extend-pathname dir (cat filename "." winner)))
       (warnings (if (atom (cdr found-exts))
                     (ok)
                   (warn :type :vl-ambiguous-load
                         :msg "Loading ~x0 based on extension order, but ~
                               there are also other matching files in this ~
                               directory.  Directory ~x0.  Matching ~
                               extensions: ~&1."
                         :args (list realfile found-exts)))))
    (mv realfile warnings)))

(define vl-find-basename/extension
  :parents (loader)
  :short "Alternative to @(see vl-find-file) that can take a list of
          extensions."
  ((filename    stringp             "Base file name to look for (no extension).")
   (extensions  string-listp        "List of extensions to try.")
   (searchcache vl-dirxlist-cache-p "Directories to search, with cached file lists.")
   (warnings    vl-warninglist-p    "Warnings accumulator."))
  :returns (mv (realpath maybe-stringp :rule-classes :type-prescription
                         "Real @('dirname/filename.ext') path to use, if found.")
               (warnings vl-warninglist-p
                         "Possibly extended with warnings about ambiguous files."))
  :measure (len (vl-dirxlist-cache-fix searchcache))
  (b* ((searchcache (vl-dirxlist-cache-fix searchcache))
       ((when (atom searchcache))
        (mv nil (ok)))
       ((cons dir dirxcache) (car searchcache))
       ((mv realfile warnings)
        (vl-find-basename/extension-aux filename extensions dir dirxcache warnings))
       ((when realfile)
        (mv realfile warnings)))
    (vl-find-basename/extension filename extensions (cdr searchcache) warnings)))

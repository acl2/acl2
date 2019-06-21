; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
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

(in-package "OSLIB")
(include-book "read-acl2-oracle")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defenum" :dir :system)

(defxdoc file-types
  :parents (oslib)
  :short "Functions for working with file types, e.g., regular files versus
directories, devices, etc."

  :long "<p>Many of these functions are just ACL2 wrappers for the Common Lisp
<a href='http://common-lisp.net/project/osicat/'>Osicat</a> library.  Unlike
the more basic file reading/writing operations (see @(see acl2::std/io)), there
is no complex logical story for reasoning about these operations.  Instead, in
the logic, practically everything here is just reading the oracle.</p>

<p>As a general rule, these functions are <b>not entirely portable</b>,
especially regarding special characters like @('~'), @('..'), @('\\'), @('*')
in path names.  Paths containing these things will certainly not behave in the
same way across different operating systems, and for that matter they may not
even behave the same way on the same operating system, but in different Lisps.
There's not much to be done for this, as the root causes are the lack of
standards among file systems and Common Lisp implementations.</p>

<p>Some possibly helpful reading about file systems in general and in Lisp:</p>

<ul>

<li>David A. Wheeler. <a
href='http://www.dwheeler.com/essays/fixing-unix-linux-filenames.html'>Fixing
Unix/Linux/POSIX Filenames: Control Characters (such as Newline), Leading
Dashes, and Other Problems</a>.</li>

<li>Peter Seibel's <a href='http://www.gigamonkeys.com/book/'>Practical Common
Lisp</a>, especially the chapters on <a
href='http://www.gigamonkeys.com/book/files-and-file-io.html'>Files and File
I/O</a> and <a
href='http://www.gigamonkeys.com/book/practical-a-portable-pathname-library.html'>Practical:
A Portable Pathname Library</a>.</li>

<li>The Common Lisp <a
href='http://www.ai.mit.edu/projects/iiip/doc/CommonLISP/HyperSpec/FrontMatter/Chapter-Index.html'>Hyperspec</a>,
especially the chapters on <a
href='http://www.ai.mit.edu/projects/iiip/doc/CommonLISP/HyperSpec/Body/chap-19.html'>file
names</a> and <a
href='http://www.ai.mit.edu/projects/iiip/doc/CommonLISP/HyperSpec/Body/chap-20.html'>files</a>.</li>

<li>The <a href='http://weitz.de/cl-fad/'>CL-FAD</a> (Common Lisp Files and
Directories) library is perhaps similar to @('osicat'), but doesn't seem to
have any support for querying what type of file you're looking at, etc., so we
don't currently use it.</li>

</ul>

<h3>Future work</h3>

<p>BOZO I would really like to have tests like -r, -w, and -x in Perl/Bash.  It
looks like osicat gives me a way to access the permissions of a file, but
these seem like just the rwx bits from the \"stat\" structure, and I don't
think that's actually tells us anything useful, unless the file happens to
be owned by us---at least, not without some way to figure out what groups
our user is in, etc.</p>

<p>The source code for Gnu's \"test\" utility (from coreutils) invokes the
EUIDACCESS system call to figure out whether the argument is readable,
writable, or executable.  So that'd probably be the nicest thing to use.  So
maybe we could rig something up with CFFI to invoke that, but I am in way over
my head here, and even if we did that, it'd probably just be a solution for
Linux.  Who knows how Windows or FreeBSD or Darwin or anything else do
it.</p>")

(local (xdoc::set-default-parents file-types))

(defenum file-kind-p
  (nil
   :regular-file
   :directory
   :symbolic-link
   :broken-symbolic-link
   :pipe
   :socket
   :character-device
   :block-device)
  :parents (file-types)
  :short "Possible return values from @(see file-kind)."
  :long "<p>Here @('nil') indicates that the file does not exist.</p>")

(local (in-theory (disable w)))

(define file-kind
  :parents (file-types)
  :short "See what kind of file a path refers to."

  ((path stringp "The path to test.")
   &key
   ((follow-symlinks booleanp) 't)
   (state 'state))
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans file-kind-p "On success: the kind of file.")
               (new-state state-p1 :hyp (force (state-p1 state))))

  :long "<p>We check whether @('path') exists.  If so, we determine what kind
of file it is.</p>

<p>This is complicated by symbolic links.  You can control how symlinks are
handled using @(':follow-symlinks').</p>

<p>By default, @(':follow-symlinks') is @('t').  In this case, the idea is to
tell you what kind of file is ultimately pointed to after resolving all the
symlinks.  Since we are following all links, we will never return
@(':symbolic-link') in this case.  However, we may return
@(':broken-symbolic-link') if there is a problem following the symlinks.</p>

<p>For finer-grained handling of symlinks, you can set @(':follow-symlinks') to
@('nil').  In this case, we return @(':symbolic-link') for all symbolic links,
no matter whether they are valid or broken.  Unless you're doing something very
fancy with symlinks, this is almost surely not what you want.</p>"
  :ignore-ok t
  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv & err state) (read-acl2-oracle state))
       ((mv & ans state) (read-acl2-oracle state)))
    (mv err (if (file-kind-p ans) ans nil) state))
  ///
  (defthm type-of-file-kind.ans
    (let ((ans (mv-nth 1 (file-kind path))))
      (and (symbolp ans)
           (not (equal ans t))))
    :rule-classes :type-prescription)

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(define path-exists-p ((path stringp) &key (state 'state))
  :parents (file-types)
  :short "Does a path exist?  After following symlinks, does it refer to
<i>any</i> \"file\" at all (a regular file, a directory, a device, ...)?"

  :long "<p>Note that we return @('nil') in the case of a broken symbolic link.
This behavior matches shell tools such as @('test -e') and seems pretty
reasonable.</p>"

  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans booleanp :rule-classes :type-prescription
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  (b* (((mv err ans state) (file-kind path))
       ((when err)
        (mv err nil state))
       (exists-p (and (not (null ans))
                      (not (eq ans :broken-symbolic-link)))))
    (mv err exists-p state))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(define paths-all-exist-p ((paths string-listp) &key (state 'state))
  :parents (file-types)
  :short "Do all of these paths <see topic='@(url path-exists-p)'>exist</see>?"
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans booleanp :rule-classes :type-prescription
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  (b* (((when (atom paths))
        (mv nil t state))
       ((mv err ans1 state) (path-exists-p (car paths)))
       ((when err)
        (mv err nil state))
       ((unless ans1)
        (mv nil nil state)))
    (paths-all-exist-p (cdr paths)))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(define paths-all-missing-p ((paths string-listp) &key (state 'state))
  :parents (file-types)
  :short "Do none of these paths <see topic='@(url path-exists-p)'>exist</see>?"
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans booleanp :rule-classes :type-prescription
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  (b* (((when (atom paths))
        (mv nil t state))
       ((mv err ans1 state) (path-exists-p (car paths)))
       ((when err)
        (mv err nil state))
       ((when ans1)
        (mv nil nil state)))
    (paths-all-missing-p (cdr paths)))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(define existing-paths ((paths string-listp) &key (state 'state))
  :parents (file-types)
  :short "Collect paths that <see topic='@(url path-exists-p)'>exist</see>."
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans string-listp :hyp (string-listp paths)
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  :verify-guards nil

  (mbe :logic
       (b* (((when (atom paths))
             (mv nil nil state))
            ((mv err exists-p state) (path-exists-p (car paths)))
            ((when err)
             (mv err nil state))
            ((mv err rest state) (existing-paths (cdr paths)))
            (ans (if exists-p
                     (cons (car paths) rest)
                   rest)))
         (mv err ans state))
       :exec
       (b* (((mv err acc state)
             (existing-paths-exec paths nil)))
         (mv err (reverse acc) state)))

  :prepwork
  ((define existing-paths-exec ((paths string-listp) acc &key (state 'state))
     "Tail recursive version for execution."
     (b* (((when (atom paths))
           (mv nil acc state))
          ((mv err exists-p state) (path-exists-p (car paths)))
          ((when err)
           (mv err acc state))
          (acc (if exists-p
                   (cons (car paths) acc)
                 acc)))
       (existing-paths-exec (cdr paths) acc))))

  ///
  (local (in-theory (enable existing-paths-exec)))

  (defthm existing-paths-exec-removal
    (equal (existing-paths-exec paths acc)
           (b* (((mv err ans state)
                 (existing-paths paths)))
             (mv err (revappend ans acc) state))))

  (defthm true-listp-of-existing-paths
    (true-listp (mv-nth 1 (existing-paths paths)))
    :rule-classes :type-prescription)

  (verify-guards existing-paths-fn)

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(define missing-paths ((paths string-listp) &key (state 'state))
  :parents (file-types)
  :short "Collect paths that do not <see topic='@(url path-exists-p)'>exist</see>."
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans string-listp :hyp (string-listp paths)
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  :verify-guards nil

  (mbe :logic
       (b* (((when (atom paths))
             (mv nil nil state))
            ((mv err exists-p state) (path-exists-p (car paths)))
            ((when err)
             (mv err nil state))
            ((mv err rest state) (missing-paths (cdr paths)))
            (ans (if exists-p
                     rest
                   (cons (car paths) rest))))
         (mv err ans state))
       :exec
       (b* (((mv err acc state)
             (missing-paths-exec paths nil)))
         (mv err (reverse acc) state)))

  :prepwork
  ((define missing-paths-exec ((paths string-listp) acc &key (state 'state))
     "Tail recursive version for execution."
     (b* (((when (atom paths))
           (mv nil acc state))
          ((mv err exists-p state) (path-exists-p (car paths)))
          ((when err)
           (mv err acc state))
          (acc (if exists-p
                   acc
                 (cons (car paths) acc))))
       (missing-paths-exec (cdr paths) acc))))

  ///
  (local (in-theory (enable missing-paths-exec)))

  (defthm missing-paths-exec-removal
    (equal (missing-paths-exec paths acc)
           (b* (((mv err ans state)
                 (missing-paths paths)))
             (mv err (revappend ans acc) state))))

  (defthm true-listp-of-missing-paths
    (true-listp (mv-nth 1 (missing-paths paths)))
    :rule-classes :type-prescription)

  (verify-guards missing-paths-fn)

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(define regular-file-p ((path stringp) &key (state 'state))
  :parents (file-types)
  :short "Does a path, after following symlinks, refer to an existing,
regular file&mdash;not to a directory, device, etc."
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans booleanp :rule-classes :type-prescription
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  (b* (((mv err ans state) (file-kind path))
       ((when err)
        (mv err nil state)))
    (mv err (eq ans :regular-file) state))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(define regular-files-p ((paths string-listp) &key (state 'state))
  :parents (file-types)
  :short "Are all of these paths <see topic='@(url regular-file-p)'>regular
files</see>?"
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans booleanp :rule-classes :type-prescription
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  (b* (((when (atom paths))
        (mv nil t state))
       ((mv err ans1 state) (regular-file-p (car paths)))
       ((when err)
        (mv err nil state))
       ((unless ans1)
        (mv nil nil state)))
    (regular-files-p (cdr paths)))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(define regular-files ((paths string-listp) &key (state 'state))
  :parents (file-types)
  :short "Collect paths that are <see topic='@(url regular-file-p)'>regular
files</see>."
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans string-listp :hyp (string-listp paths)
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  :verify-guards nil

  (mbe :logic
       (b* (((when (atom paths))
             (mv nil nil state))
            ((mv err regular-p state) (regular-file-p (car paths)))
            ((when err)
             (mv err nil state))
            ((mv err rest state) (regular-files (cdr paths)))
            (ans (if regular-p
                     (cons (car paths) rest)
                   rest)))
         (mv err ans state))
       :exec
       (b* (((mv err acc state)
             (regular-files-exec paths nil)))
         (mv err (reverse acc) state)))

  :prepwork
  ((define regular-files-exec ((paths string-listp) acc &key (state 'state))
     "Tail recursive version for execution."
     (b* (((when (atom paths))
           (mv nil acc state))
          ((mv err regular-p state) (regular-file-p (car paths)))
          ((when err)
           (mv err acc state))
          (acc (if regular-p
                   (cons (car paths) acc)
                 acc)))
       (regular-files-exec (cdr paths) acc))))

  ///
  (local (in-theory (enable regular-files-exec)))

  (defthm regular-files-exec-removal
    (equal (regular-files-exec paths acc)
           (b* (((mv err ans state)
                 (regular-files paths)))
             (mv err (revappend ans acc) state))))

  (defthm true-listp-of-regular-files
    (true-listp (mv-nth 1 (regular-files paths)))
    :rule-classes :type-prescription)

  (verify-guards regular-files-fn)

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))



(define directory-p ((path stringp) &key (state 'state))
  :parents (file-types)
  :short "Does a path, after following symlinks, refer to a directory?"
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans booleanp :rule-classes :type-prescription
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  (b* (((mv err ans state) (file-kind path))
       ((when err)
        (mv err nil state)))
    (mv err (eq ans :directory) state))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))

(define directories-p ((paths string-listp) &key (state 'state))
  :parents (file-types)
  :short "Are all of these paths <see topic='@(url
directory-p)'>directories</see>?"
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans booleanp :rule-classes :type-prescription
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  (b* (((when (atom paths))
        (mv nil t state))
       ((mv err ans1 state) (directory-p (car paths)))
       ((when err)
        (mv err nil state))
       ((unless ans1)
        (mv nil nil state)))
    (directories-p (cdr paths)))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))

(define directories ((paths string-listp) &key (state 'state))
  :parents (file-types)
  :short "Collect paths that are <see topic='@(url
directory-p)'>directories</see>."
  :returns (mv (err "NIL on success, or an error @(see msg) on failure.")
               (ans string-listp :hyp (string-listp paths)
                    "Meaningful only when there is no error.")
               (new-state state-p1 :hyp (force (state-p1 state))))
  :verify-guards nil

  (mbe :logic
       (b* (((when (atom paths))
             (mv nil nil state))
            ((mv err directory-p state) (directory-p (car paths)))
            ((when err)
             (mv err nil state))
            ((mv err rest state) (directories (cdr paths)))
            (ans (if directory-p
                     (cons (car paths) rest)
                   rest)))
         (mv err ans state))
       :exec
       (b* (((mv err acc state)
             (directories-exec paths nil)))
         (mv err (reverse acc) state)))

  :prepwork
  ((define directories-exec ((paths string-listp) acc &key (state 'state))
     "Tail recursive version for execution."
     (b* (((when (atom paths))
           (mv nil acc state))
          ((mv err directory-p state) (directory-p (car paths)))
          ((when err)
           (mv err acc state))
          (acc (if directory-p
                   (cons (car paths) acc)
                 acc)))
       (directories-exec (cdr paths) acc))))

  ///
  (local (in-theory (enable directories-exec)))

  (defthm directories-exec-removal
    (equal (directories-exec paths acc)
           (b* (((mv err ans state)
                 (directories paths)))
             (mv err (revappend ans acc) state))))

  (defthm true-listp-of-directories
    (true-listp (mv-nth 1 (directories paths)))
    :rule-classes :type-prescription)

  (verify-guards directories-fn)

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))

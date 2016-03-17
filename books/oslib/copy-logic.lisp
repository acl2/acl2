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
(include-book "dirname-logic")
(include-book "ls-logic")
(include-book "file-types-logic")
(include-book "mkdir-logic")
(include-book "std/util/defines" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(set-state-ok t)

(define copy-file
  :parents (copy)
  :short "Copy a single file. (low level)"
  ((from stringp "Path to copy from, should be an ordinary file.")
   (to   stringp "Path to copy to, should <b>not</b> be a directory.")
   &key
   ((overwrite booleanp "Should we overwrite @('to'), if it exists?") 'nil)
   (state 'state))
  :returns
  (mv (error "NIL on success, or an error @(see msg) on failure.")
      (state state-p1 :hyp (force (state-p1 state))))
  (declare (ignorable from to overwrite))
  :long "<p>This is a low level function for copying files.  See @(see copy)
for a higher-level alternative that can, e.g., copy directories.</p>

<p>In the logic this function reads from the ACL2 oracle.  In the execution we
use raw Lisp functions to attempt to copy the indicated file.  This can fail
for many reasons, e.g., @('from') might not exist or we might not have
permission to copy it.</p>

<p>Some typical examples of how to use this command correctly would be:</p>

@({
     (copy-file \"original.txt\" \"backup.txt\")

     (copy-file \"/home/jared/original.txt\"
                \"/home/jared/my-backups/today/original.txt\"
                :overwrite t)
})

<p>The following example is <b>not correct and will fail</b> because the
destination is a directory:</p>

@({
     (copy-file \"original.txt\" \"/home/jared/\") ;; wrong, fails
})

<p>Probably what was intended is instead:</p>

@({
     (copy-file \"original.txt\"              ;; correct: specify full
                \"/home/jared/original.txt\") ;; destination path
})"

  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv ?err val state) (read-acl2-oracle state)))
    (mv val state)))



(define copy-file-list
  ;; Implementation function, do not call directly.
  ((fromdir   stringp      "Directory where these files currently live.")
   (fromnames string-listp "Names of the files in fromdir to copy.")
   (todir     stringp      "Directory to copy the files to (should already exist).")
   &key
   ((overwrite booleanp) 'nil)
   (state                'state))
  :returns (mv (error "NIL on success, or an error @(see msg) on failure.")
               (state state-p1 :hyp (force (state-p1 state))))
  (b* (((when (atom fromnames))
        (mv nil state))
       (full-from1 (catpath fromdir (car fromnames)))
       (full-to1   (catpath todir   (car fromnames)))
       ((mv err state) (copy-file full-from1 full-to1 :overwrite overwrite))
       ((when err)
        (mv err state)))
    (copy-file-list fromdir (cdr fromnames) todir :overwrite overwrite)))


(defines copy-recursively
  ;; Implementation function, do not call directly.
  (define copy-directory-recursively
    ((fromdir stringp "Directory whose contents we want to copy.")
     (todir   stringp "Full name of target directory to copy to.")
     &key
     (limit natp "Maximum number of directories to descend into.")
     (state 'state))
    :returns (mv (error "NIL on success, or an error @(see msg) on failure.")
                 (state state-p1 :hyp (force (state-p1 state))))
    :measure (acl2::two-nats-measure limit 0)
    (b* (((when (zp limit))
          (mv (msg "~s0: too many levels of recursion while copying ~s1.  Looping symlinks?"
                   __function__ fromdir)
              state))

         ((mv err from-files state) (ls-files fromdir))
         ((when err)
          (mv (msg "~s0: Error listing files in ~s1: ~@2" __function__ fromdir err)
              state))
         ((mv err from-subdirs state) (ls-subdirs fromdir))
         ((when err)
          (mv (msg "~s0: Error listing subdirectories in ~s1: ~@2" __function__ fromdir err)
              state))

         ;; Make sure todir exists or create it
         ((mv err to-kind state) (file-kind todir))
         ((when err)
          (mv (msg "~s0: Error checking type of ~s1: ~@2" __function__ todir err)
              state))
         ((unless (or (not to-kind)
                      (eq to-kind :directory)))
          (mv (msg "~s0: Expected ~s1 to be a directory but it is a ~s2?" __function__ todir to-kind)
              state))

         ;; Create the target directory if necessary
         ((mv okp state)
          (if (not to-kind)
              (mkdir todir)
            (mv t state)))
         ((unless okp)
          (mv (msg "~s0: Failed to create directory ~s1." __function__ todir)
              state))

         ;; Copy all the files into the target dir.
         ((mv files-err state) (copy-file-list fromdir from-files todir))
         ((when files-err) (mv files-err state))

         ;; And recursively copy all of the subdirectories.
         ((mv dirs-err state) (copy-directory-list-recursively fromdir from-subdirs todir
                                                               :limit (- limit 1)))
         ((when dirs-err) (mv dirs-err state)))

      ;; Copied everything and it all worked.  Woohoo.
      (mv nil state)))

  (define copy-directory-list-recursively
    ((fromdir stringp      "Root directory being copied from.")
     (subdirs string-listp "List of immediate subdirectories of fromdir.")
     (todir   stringp      "Target directory to copy to (should have just been created).")
     &key
     (limit  natp)
     (state 'state))
    :returns (mv (error "NIL on success, or an error @(see msg) on failure.")
                 (state state-p1 :hyp (force (state-p1 state))))
    :measure (acl2::two-nats-measure limit (len subdirs))
    (b* (((when (atom subdirs))
          ;; Done copying everything.
          (mv nil state))
         ((mv err1 state)
          (copy-directory-recursively (catpath fromdir (car subdirs))
                                      (catpath todir   (car subdirs))
                                      :limit limit))
         ((when err1)
          (mv err1 state)))
      (copy-directory-list-recursively fromdir (cdr subdirs) todir :limit limit))))


(define nice-copy-single-file
  ;; Implementation function, do not call directly.
  ;; Copy a single file.
  ((from stringp "Path to copy from (assumed to be a regular file that exists).")
   (to   stringp "Path to copy to   (hasn't yet been examined).")
   &key
   (overwrite booleanp)
   (state     'state))
  :returns (mv (error "NIL on success, or an error @(see msg) on failure.")
               (state state-p1 :hyp (force (state-p1 state))))
  (b* (((mv to-err to-kind state) (file-kind to))
       ((when to-err) (mv to-err state))

       ((unless to-kind)
        ;; Trying to write a file to somewhere that doesn't yet exist.  That
        ;; seems fine.
        (copy-file from to :overwrite overwrite))

       ((when (eq to-kind :regular-file))
        (if overwrite
            (copy-file from to :overwrite overwrite)
          (mv (msg "~s0: destination already exists: ~s1" 'copy to)
              state)))

       ((unless (eq to-kind :directory))
        ;; Destination exists but isn't a regular file or a directory?  It must
        ;; be some kind of weird thing like a pipe, socket, device.  Let's not
        ;; try to overwrite it.
        (mv (msg "~s0: can't overwrite ~s1: ~s2" 'copy to-kind to)
            state))

       ;; Trying to copy a file (hello.txt) into an existing directory (/foo).
       ;; So the real destination is /foo/hello.txt.
       ((mv err basename state) (basename from))
       ((when err)
        (mv (msg "~s0: can't figure out base name of file ~s1: ~@2."
                 'copy from err)
            state))
       (to (catpath to basename))

       ((mv to-err to-kind state) (file-kind to))
       ((when to-err) (mv to-err state))

       ((unless to-kind)
        ;; Fine, the real dest doesn't exist yet, not overwriting anything.
        (copy-file from to :overwrite overwrite))

       ((when (eq to-kind :regular-file))
        (if overwrite
            (copy-file from to :overwrite overwrite)
          (mv (msg "~s0: destination already exists: ~s1" 'copy to)
              state))))

    ;; Otherwise we're trying to overwrite something else (a directory, or
    ;; maybe something tricky like a pipe/socket/etc), which is too scary, so
    ;; just fail.
    (mv (msg "~s0: can't overwrite ~s1: ~s2" 'copy to-kind to) state)))


(define nice-copy-single-directory
  ;; Implementation function, do not call directly.
  ;; Copy a whole directory.
  ;; Assumes recursion is okay.
  ((from stringp "Path to copy from (assumed to be a directory that exists).")
   (to   stringp "Path to copy to   (hasn't yet been examined).")
   &key
   (limit natp)
   (state 'state))
  :returns (mv (error "NIL on success, or an error @(see msg) on failure.")
               (state state-p1 :hyp (force (state-p1 state))))
  (b* (((mv to-err to-kind state) (file-kind to))
       ((when to-err) (mv to-err state))

       ((unless to-kind)
        ;; Trying to write a place that doesn't exist yet.  That's all fine.
        (copy-directory-recursively from to :limit limit))

       ((unless (eq to-kind :directory))
        ;; Trying to overwrite a regular file or some other kind of fancy
        ;; file (socket, pipe, device) with a directory?  Can't do that.
        (mv (msg "~s0: can't overwrite ~s1 with directory ~s2" 'copy to from)
            state))

       ;; Otherwise, trying to copy a directory (foo) into a directory (bar).
       ;; That's ok, we just want to create bar/foo.  To do that we need to
       ;; know the basename of foo, as in nice-single-copy-file.
       ((mv err basename state) (basename from))
       ((when err)
        (mv (msg "~s0: can't figure out base name of directory ~s1: ~@2."
                 'copy from err)
            state))
       (to (catpath to basename))

       ((mv to-err to-kind state) (file-kind to))
       ((when to-err) (mv to-err state))

       ((unless to-kind)
        ;; Fine, the real dest doesn't exist
        (copy-directory-recursively from to :limit limit)))

    ;; Otherwise, we're trying to copy foo into bar/foo, but bar/foo already
    ;; exists.  We'll just fail.
    (mv (msg "~s0: can't overwrite ~s1 with directory ~s2" 'copy to from)
        state)))

(define copy
  :parents (oslib)
  :short "Copy files or directories, with recoverable errors."
  ((from stringp "Path to copy from (ordinary file or directory).")
   (to   stringp "Path to copy to   (ordinary file or directory).")
   &key
   ((recursive booleanp "Allow copying directories like @('cp -r')?") 'nil)
   ((overwrite booleanp "Should we overwrite files/directories that already exist?
                         Only matters when copying individual files, not directories.") 'nil)
   ((limit     natp     "Directly depth recursion limit (in case of symlink loops).
                         Only matters when copying directories, not files.") '1000)
   (state 'state))
  :returns
  (mv (error "NIL on success, or an error @(see msg) on failure.")
      (state state-p1 :hyp (force (state-p1 state))))

  :long "<p>This is a nice, higher-level wrapper around the low-level @(see
copy-file) routine, which acts more like the unix @('cp') shell command.  It
can (optionally) copy whole directories recursively, and more correctly handles
copying individual files into an existing directory.</p>

<p>Copying files can fail for a variety of reasons.  This function attempts to
gracefully catch errors and return them in a form that you can recover from.
See also @(see copy!), an alternative that just causes a hard error if there is
any problem.</p>

<p>Examples:</p>

<dl>

<dt>@('(oslib::copy \"./hello.txt\" \"./hello-copy.txt\")')</dt>
<dd>copies hello.txt to hello-copy.txt</dd>
<dd>\"safe\", won't overwrite hello-copy.txt if it exists</dd>

<dt>@('(oslib::copy \"./hello.txt\" \"./hello-copy.txt\" :overwrite t)')</dt>
<dd>copies hello.txt to hello-copy.txt</dd>
<dd>overwrites hello-copy.txt if it exists</dd>
<dd>won't overwrite directories, pipes, sockets, etc.</dd>

<dt>@('(oslib::copy \"./hello.txt\" \"./foo/\")')</dt>
<dd>copies hello.txt to foo/hello.txt</dd>
<dd>won't overwrite foo/hello.txt if it exists</dd>


<dt>@('(oslib::copy \"./foo/\" \"./bar/\")')</dt>
<dd>Recursively copy the directory @('foo') to...
<ul>
 <li>If directory @('bar') exists: @('bar/foo')</li>
 <li>Otherwise, @('bar')</li>
</ul></dd>
<dd>Won't overwrite @('./bar/foo') if it already exists.</dd>
<dd>Won't overwrite @('./bar') if it is some non-directory file.</dd>

</dl>"

  (b* (((mv from-err from-kind state) (file-kind from)) ;; follows symlinks
       ((when from-err)
        (mv (msg "~s0: can't copy ~s1: ~@2" 'copy from from-err) state))

       ((unless from-kind)
        (mv (msg "~s0: no such file: ~s1" 'copy from) state))

       ((when (eq from-kind :regular-file))
        (nice-copy-single-file from to :overwrite overwrite))

       ((when (eq from-kind :directory))
        (if (not recursive)
            (mv (msg "~s0: can't copy directory (in non-recursive mode): ~s1" 'copy from)
                state)
          (nice-copy-single-directory from to :limit limit))))

    ;; Let's not try to copy weird files (pipes, sockets, etc.)
    (mv (msg "~s0: unsupported file type ~s1: ~s2" 'copy from-kind from)
        state)))

(define copy!
  :parents (oslib)
  :short "Copy files or directories, or cause a hard error."
  ((from stringp "Path to copy from (ordinary file or directory).")
   (to   stringp "Path to copy to   (ordinary file or directory).")
   &key
   ((recursive booleanp "Allow copying directories like @('cp -r')?") 'nil)
   ((overwrite booleanp "Should we overwrite files/directories that already exist?
                         Only matters when copying individual files, not directories.") 'nil)
   ((limit     natp     "Directly depth recursion limit (in case of symlink loops).
                         Only matters when copying directories, not files.") '1000)
   (state 'state))
  :returns
  (state state-p1 :hyp (force (state-p1 state)))
  :long "<p>This is identical to @(see copy) except that we raise a hard error
if anything goes wrong.</p>"
  (b* (((mv err state) (copy from to
                             :recursive recursive
                             :overwrite overwrite
                             :limit limit))
       ((when err)
        (raise "~@0" err)
        state))
    state))


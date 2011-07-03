; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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

; ls.lisp -- functions to list the contents of directories

(in-package "ACL2")
(include-book "tools/mv-nth" :dir :system)

(defund remove-nonstrings (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((stringp (car x))
         (cons (car x) (remove-nonstrings (cdr x))))
        (t
         (remove-nonstrings (cdr x)))))

(defthm string-listp-of-remove-nonstrings
  (string-listp (remove-nonstrings x))
  :hints(("Goal" :in-theory (enable remove-nonstrings))))


(defttag ls)

(remove-untouchable 'read-acl2-oracle t)


(defund ls-subdirs (path state)
  ":Doc-Section Programming
   Get a subdirectory listing.~/

   General form:
   ~bv[]
     (ls-subdirs path state) --> (mv error val state)
   ~ev[]

   Example:
   ~bv[]
     (ls-subdirs \"/home/users/jared\" state)
   ~ev[]

   In the logic this function reads from the ACL2 oracle.  In the execution we
   query the file system to obtain a listing of the subdirectories of the given
   ~c[path].  We believe this is sound.

   On success, ~c[error] is ~c[nil] and ~c[val] is a list of strings that are
   the names of the immediate subdirectories of ~c[path].  These names are
   ~st[not] complete paths, i.e., if ~c[/home/users/jared] contains directories
   named ~c[foo] and ~c[bar], then the resulting ~c[val] will have ~c[\"foo\"]
   and ~c[\"bar\"], not something like ~c[\"/home/users/jared/foo\"].

   On failure, ~c[error] is ~c[t] and ~c[val] is a string that describes the
   problem.  For instance, perhaps ~c[path] does not exist or is not readable
   by the current user.

   Notes.

     The given ~c[path] need not contain a trailing slash, but it is fine to
     include one.

     You can use standard Unix idioms like ~c[~~] and ~c[~~jared].

     If ~c[path] is the empty string, it is interpreted as the current
     directory.~/~/"

  (declare (xargs :stobjs state
                  :guard (stringp path))
           (ignorable path))
  (mv-let (err val state)
          (read-acl2-oracle state)
          (mv (if err t nil)
              (if err
                  (if (stringp val) val "error")
                (remove-nonstrings val))
              state)))

(local (in-theory (enable ls-subdirs)))

(defthm booleanp-of-ls-subdirs
  (booleanp (mv-nth 0 (ls-subdirs path state)))
  :rule-classes :type-prescription)

(defthm stringp-of-ls-subdirs
  (equal (stringp (mv-nth 1 (ls-subdirs path state)))
         (mv-nth 0 (ls-subdirs path state))))

(defthm string-listp-of-ls-subdirs
  (equal (string-listp (mv-nth 1 (ls-subdirs path state)))
         (not (mv-nth 0 (ls-subdirs path state)))))

(defthm state-p1-of-ls-subdirs
  (implies (force (state-p1 state))
           (state-p1 (mv-nth 2 (ls-subdirs path state))))
  :hints(("Goal" :in-theory (enable read-acl2-oracle))))

(progn!
 (set-raw-mode t)

 (defun ls-subdirs (path state)

   #-(and Clozure Unix)
   (mv t "ls-subdirs: not yet implemented on this lisp." state)

   #+(and Clozure Unix)
   (let ((results (handler-case
                   (let* ((truename (truename (parse-namestring path)))
                          (pattern  (concatenate 'string (namestring truename) "*.*"))
                          (files    (directory pattern
                                               :directories t
                                               :files nil
                                               :all t))
                          (names    (loop for f in files
                                          collect
                                          (car (last (pathname-directory f))))))
                     names)
                   (error (condition)
                          (format nil "ls-subdirs: ~a" condition)))))
     (cond ((stringp results)
            (mv t results state))
           ((string-listp results)
            (mv nil results state))
           (t
            (mv nil (format nil "Expected string list, found ~a.~%" results)
                state))))))



(defund ls-files (path state)
  ":Doc-Section Programming
   Get a file listing.~/

   General form:
   ~bv[]
     (ls-files path state) --> (mv error val state)
   ~ev[]

   Example:
   ~bv[]
     (ls-files \"/home/users/jared\" state)
   ~ev[]

   In the logic this function reads from the ACL2 oracle.  In the execution we
   query the file system to obtain a listing of the subdirectories of the given
   ~c[path].  We believe this is sound.

   On success, ~c[error] is ~c[nil] and ~c[val] is a list of strings that are
   the names of the files contained in ~c[path].  These names are ~st[not]
   complete paths, i.e., if ~c[/home/users/jared] contains ~c[foo.txt] and
   ~c[Makefile], then the resulting ~c[paths] will be ~c[\"foo.txt\"] and
   ~c[\"Makefile\"], not something like ~c[\"/home/users/jared/foo.txt\"].

   On failure, ~c[error] is ~c[t] and ~c[val] is a string that describes the
   problem.  The ~c[paths] returned are full paths with trailing slashes.

   Notes.

     The given ~c[path] need not contain a trailing slash, but it is fine to
     include one.

     You can use standard Unix idioms like ~c[~~] and ~c[~~jared].

     If ~c[path] is the empty string, it is interpreted as the current
     directory.~/~/"

  (declare (xargs :stobjs state
                  :guard (stringp path))
           (ignorable path))
  (mv-let (err val state)
          (read-acl2-oracle state)
          (mv (if err t nil)
              (if err
                  (if (stringp val) val "error")
                (remove-nonstrings val))
              state)))

(local (in-theory (enable ls-files)))

(defthm booleanp-of-ls-files
  (booleanp (mv-nth 0 (ls-files path state)))
  :rule-classes :type-prescription)

(defthm stringp-of-ls-files
  (equal (stringp (mv-nth 1 (ls-files path state)))
         (mv-nth 0 (ls-files path state))))

(defthm string-listp-of-ls-files
  (equal (string-listp (mv-nth 1 (ls-files path state)))
         (not (mv-nth 0 (ls-files path state)))))

(defthm state-p1-of-ls-files
  (implies (force (state-p1 state))
           (state-p1 (mv-nth 2 (ls-files path state))))
  :hints(("Goal" :in-theory (enable read-acl2-oracle))))

(progn!
 (set-raw-mode t)

 #+(and Clozure Unix)
 (defmacro ccl-native-translated-namestring (x)
   `(,(intern "NATIVE-TRANSLATED-NAMESTRING" "CCL") ,x))

 (defun ls-files (path state)

   #-(and Clozure Unix)
   (mv t "ls-files: not yet implemented on this lisp." state)

   #+(and Clozure Unix)
   (let ((results (handler-case
                   (let* ((truename (truename (parse-namestring path)))
                          (pattern  (concatenate 'string (namestring truename)
                                                 "*.*"))
                          (files    (directory pattern
                                               :directories nil
                                               :files t
                                               :all t))
                          (names    (loop for f in files
                                          collect
                                          (ccl-native-translated-namestring
                                           (file-namestring f)))))
                     names)
                   (error (condition)
                          (format nil "ls-files: ~a" condition)))))
     (cond ((stringp results)
            (mv t results state))
           ((string-listp results)
            (mv nil results state))
           (t
            (mv nil (format nil "Expected string list, found ~a.~%" results)
                state))))))
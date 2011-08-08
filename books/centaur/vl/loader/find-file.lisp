; VL Verilog Toolkit
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

(in-package "VL")
(include-book "../util/defs")
(local (include-book "unicode/open-input-channel" :dir :system))
(local (include-book "unicode/close-input-channel" :dir :system))
(local (include-book "../util/arithmetic"))
(set-state-ok t)


(defsection vl-extend-pathname
  :parents (vl-find-file)
  :short "@(call vl-extend-pathname) concatenates <tt>dir</tt> and
<tt>filename</tt>, adding a slash to between them only if <tt>dir</tt> does not
end with a slash."

  (defund vl-ends-with-directory-separatorp (x)
    (declare (xargs :guard (stringp x)))
    (let ((len (length x)))
      (and (/= len 0)
           (eql (char x (- (length x) 1)) ACL2::*directory-separator*))))

  (defund vl-extend-pathname (dir filename)
    (declare (xargs :guard (and (stringp dir)
                                (stringp filename))))
    (str::cat dir
              (if (vl-ends-with-directory-separatorp dir)
                  ""
                (coerce (list ACL2::*directory-separator*) 'string))
              filename))

  (defthm stringp-of-vl-extend-pathname
    (stringp (vl-extend-pathname dir filename))
    :rule-classes :type-prescription))



(defsection vl-find-file-aux
  :parents (vl-find-file)
  :short "Look for a file in a list of search directories."

  (defund vl-find-file-aux (filename searchpath state)
    (declare (xargs :guard (and (stringp filename)
                                (string-listp searchpath)
                                (state-p state))
                    :verify-guards nil))
    (b* (((when (atom searchpath))
          (mv nil state))
         (attempt (vl-extend-pathname (car searchpath) filename))
         ((mv channel state)
          (open-input-channel attempt :character state))
         ((unless channel)
          (vl-find-file-aux filename (cdr searchpath) state))
         (state (close-input-channel channel state)))
      (mv attempt state)))

  (defthm state-p1-of-vl-find-file-aux
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (vl-find-file-aux filename searchpath state))))
    :hints(("Goal" :in-theory (e/d (vl-find-file-aux)))))

  (defthm stringp-of-vl-find-file-aux
    (equal (stringp (mv-nth 0 (vl-find-file-aux filename searchpath state)))
           (if (mv-nth 0 (vl-find-file-aux filename searchpath state))
               t
             nil))
    :hints(("Goal" :in-theory (enable vl-find-file-aux))))

  (verify-guards vl-find-file-aux))



(defsection vl-find-file
  :parents (loader)
  :short "Determine where to load a file from, given its (absolute or relative)
name and a list of directories to search."

  :long "<p><b>Signature:</b> @(call vl-find-file) returns <tt>(mv realname
state)</tt>.</p>

<p>The <tt>filename</tt> is the name of a file you want to load; it can be
either an absolute filename (in which case it will just be returned as
<tt>realname</tt>), or a relative filename (in which case we will look for it
in the <tt>searchpath</tt>).</p>

<p>The <tt>searchpath</tt> is a list of strings that are the names of
directories to search.  These order of these directories is important, because
we search them in order.</p>

<p>If we find the file in any of the search directories, we essentially return
<tt>dir/filename</tt> as <tt>realname</tt>.  But if we can't find the file
anywhere, <tt>realname</tt> is just <tt>nil</tt>.</p>"

  (defund vl-find-file (filename searchpath state)
    (declare (xargs :guard (and (stringp filename)
                                (string-listp searchpath)
                                (state-p state))
                    :guard-hints(("Goal" :in-theory (enable state-p1)))))
    (if (ACL2::absolute-pathname-string-p filename nil (ACL2::os (w state)))
        (mv filename state)
      (vl-find-file-aux filename searchpath state)))

  (in-theory (disable ACL2::absolute-pathname-string-p ACL2::os ACL2::w))

  (defthm state-p1-of-vl-find-file
    (implies (and (force (state-p1 state))
                  (force (stringp filename)))
             (state-p1 (mv-nth 1 (vl-find-file filename searchpath state))))
    :hints(("Goal" :in-theory (enable vl-find-file))))

  (defthm stringp-of-vl-find-file
    (implies (force (stringp filename))
             (equal (stringp (mv-nth 0 (vl-find-file filename searchpath state)))
                    (if (mv-nth 0 (vl-find-file filename searchpath state))
                        t
                      nil)))
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary
                    (implies (force (stringp filename))
                             (or (not (mv-nth 0 (vl-find-file filename searchpath state)))
                                 (stringp (mv-nth 0 (vl-find-file filename searchpath state)))))))
    :hints(("Goal" :in-theory (enable vl-find-file)))))


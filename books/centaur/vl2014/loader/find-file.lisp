; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "../util/warnings")
(local (include-book "std/io/base" :dir :system))
(local (include-book "../util/arithmetic"))
(set-state-ok t)


(defsection vl-extend-pathname
  :parents (vl-find-file)
  :short "@(call vl-extend-pathname) concatenates @('dir') and @('filename'),
adding a slash to between them only if @('dir') does not end with a slash."

  (defund vl-ends-with-directory-separatorp (x)
    (declare (xargs :guard (stringp x)))
    (let ((len (length x)))
      (and (/= len 0)
           (eql (char x (- (length x) 1)) ACL2::*directory-separator*))))

  (defund vl-extend-pathname (dir filename)
    (declare (xargs :guard (and (stringp dir)
                                (stringp filename))))
    (cat dir
         (if (vl-ends-with-directory-separatorp dir)
             ""
           (implode (list ACL2::*directory-separator*)))
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

  :long "<p><b>Signature:</b> @(call vl-find-file) returns @('(mv realname
state)').</p>

<p>The @('filename') is the name of a file you want to load; it can be either
an absolute filename (in which case it will just be returned as @('realname')),
or a relative filename (in which case we will look for it in the
@('searchpath')).</p>

<p>The @('searchpath') is a list of strings that are the names of directories
to search.  These order of these directories is important, because we search
them in order.</p>

<p>If we find the file in any of the search directories, we essentially return
@('dir/filename') as @('realname').  But if we can't find the file anywhere,
@('realname') is just @('nil').</p>"

  (defund vl-find-file (filename searchpath state)
    (declare (xargs :guard (and (stringp filename)
                                (string-listp searchpath)
                                (state-p state))
                    :guard-hints(("Goal" :in-theory (enable state-p1 get-global
                                                            put-global)))))
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



(defsection vl-find-basename/extension
  :parents (loader)
  :short "Alternative to @(see vl-find-file) that can take a list of
extensions."

  :long "<p><b>Signature:</b> @(call vl-find-basename/extension) returns @('(mv
realname warnings state)').</p>"

  (defund vl-find-basename/extension-aux (filename extensions dir state)
    (declare (xargs :guard (and (stringp filename)
                                (string-listp extensions)
                                (stringp dir)
                                (state-p state))))
    (b* (((when (atom extensions))
          (mv nil state))
         ((mv rest state)
          (vl-find-basename/extension-aux filename (cdr extensions) dir state))
         (filename1 (cat filename "." (car extensions)))
         (attempt   (vl-extend-pathname dir filename1))
         ((mv channel state)
          (open-input-channel attempt :character state))
         (state
          (if channel
              (close-input-channel channel state)
            state)))
      (mv (if channel (cons attempt rest) rest)
          state)))

  (local (in-theory (enable vl-find-basename/extension-aux)))

  (defthm true-listp-of-vl-find-basename/extension-aux
    (true-listp (mv-nth 0 (vl-find-basename/extension-aux filename extensions dir state)))
    :rule-classes :type-prescription)

  (defthm state-p1-of-vl-find-basename/extension-aux
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (vl-find-basename/extension-aux filename extensions dir state)))))

  (defthm string-listp-of-vl-find-basename/extension-aux
    (string-listp (mv-nth 0 (vl-find-basename/extension-aux filename extensions dir state))))

  (local (in-theory (disable vl-find-basename/extension-aux)))


  (defund vl-find-basename/extension (filename extensions searchpath warnings state)
    (declare (xargs :guard (and (stringp filename)
                                (string-listp extensions)
                                (string-listp searchpath)
                                (vl-warninglist-p warnings)
                                (state-p state))))
    (b* (((when (atom searchpath))
          (mv nil warnings state))
         ((mv hits state)
          (vl-find-basename/extension-aux filename extensions (car searchpath) state))
         ((unless hits)
          (vl-find-basename/extension filename extensions (cdr searchpath) warnings state))
         (warnings
          (if (atom (cdr hits))
              warnings
            (cons (make-vl-warning
                   :type :vl-ambiguous-load
                   :msg "Loading ~x0 based on extension order, but there are ~
                       also other matching files in this directory: ~&1."
                   :args (list (car hits) (cdr hits))
                   :fatalp nil
                   :fn 'vl-find-basename/extension)
                  warnings))))
      (mv (car hits) warnings state)))

  (local (in-theory (enable vl-find-basename/extension)))

  (defthm state-p1-of-vl-find-basename/extension
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 2 (vl-find-basename/extension filename extensions searchpath warnings state)))))

  (defthm vl-warninglist-p-of-vl-find-basename/extension
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-find-basename/extension filename extensions searchpath warnings state)))))

  (local (defthm crock
           (implies (string-listp x)
                    (equal (stringp (car x))
                           (if x t nil)))))

  (local (defthm crock2
           (implies (string-listp x)
                    (iff (car x)
                         (consp x)))))

  (defthm stringp-of-vl-find-basename/extension
    (equal (stringp (mv-nth 0 (vl-find-basename/extension filename extensions searchpath warnings state)))
           (if (mv-nth 0 (vl-find-basename/extension filename extensions searchpath warnings state))
               t
             nil))
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary
                    (or (not (mv-nth 0 (vl-find-basename/extension filename extensions searchpath warnings state)))
                        (stringp (mv-nth 0 (vl-find-basename/extension filename extensions searchpath warnings state))))))))

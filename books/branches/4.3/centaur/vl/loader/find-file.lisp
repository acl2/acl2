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
  :rule-classes :type-prescription)


(encapsulate
  ()
  (defund vl-find-file-aux (filename searchpath state)
    (declare (xargs :guard (and (stringp filename)
                                (string-listp searchpath)
                                (state-p state))
                    :verify-guards nil))
    (if (atom searchpath)
        (mv nil state)
      (let ((attempt (vl-extend-pathname (car searchpath) filename)))
        (mv-let (channel state)
          (open-input-channel attempt :character state)
          (if channel
              (let ((state (close-input-channel channel state)))
                (mv attempt state))
            (vl-find-file-aux filename (cdr searchpath) state))))))

  (local (defthm state-p1-of-vl-find-file-aux
           (implies (force (state-p1 state))
                    (state-p1 (mv-nth 1 (vl-find-file-aux filename searchpath state))))
           :hints(("Goal" :in-theory (e/d (vl-find-file-aux))))))

  (local (defthm stringp-of-vl-find-file-aux
           (equal (stringp (mv-nth 0 (vl-find-file-aux filename searchpath state)))
                  (if (mv-nth 0 (vl-find-file-aux filename searchpath state))
                      t
                    nil))
           :hints(("Goal" :in-theory (enable vl-find-file-aux)))))

  (verify-guards vl-find-file-aux)

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


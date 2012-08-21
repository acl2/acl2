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
; date.lisp -- Get the current date/time within ACL2.
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "str/natstr" :dir :system)
(include-book "str/cat" :dir :system)

(defttag date)

(remove-untouchable read-acl2-oracle t)

(defun date (state)
  ":Doc-Section Programming
Get a datestamp like \"November 17, 2010 10:25:33\"~/

~bv[]
 (date state) --> (mv \"November 17, 2010 10:25:33\" state)
~ev[]

In the logic this function reads from the ACL2 oracle.  In the execution we use
Common Lisp's ~c[get-decoded-time] function to figure out what the current date
and time is.  Although this requires a ttag, we believe it is sound.~/~/"

  (declare (xargs :stobjs state))
  (mv-let (erp val state)
    (read-acl2-oracle state)
    (declare (ignore erp))
    (if (stringp val)
        (mv val state)
      (mv "Error reading date." state))))

(defthm stringp-of-date
  (stringp (mv-nth 0 (date state))))

(defthm state-p1-of-date
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (date state))))
  :hints(("Goal" :in-theory (enable read-acl2-oracle))))

(progn!
 (set-raw-mode t)
 (defun date (state)
   (unless (live-state-p state)
     (er hard? 'date "Date can only be called on a live state.")
     (mv "Error reading date." state))
   (multiple-value-bind
    (second minute hour date month year day daylight-p zone)
    (get-decoded-time)
    (declare (ignore daylight-p zone day))
    (let ((month (nth (- month 1) '("January" "February" "March" "April" "May"
                                    "June" "July" "August" "September" "October"
                                    "November" "December")))
          (year    (str::natstr year))
          (date    (str::natstr date))
          (hour    (if (< hour 10)
                       (str::cat "0" (str::natstr hour))
                     (str::natstr hour)))
          (minute  (if (< minute 10)
                       (str::cat "0" (str::natstr minute))
                     (str::natstr minute)))
          (second  (if (< second 10)
                       (str::cat "0" (str::natstr second))
                     (str::natstr second))))
      (mv (str::cat month " " date ", " year " " hour ":" minute ":" second)
          state)))))

(defttag nil)

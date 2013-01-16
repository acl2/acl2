; OSLIB -- Operating System Utilities
; Copyright (C) 2013 Centaur Technology
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

(in-package "OSLIB")

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
          state))))
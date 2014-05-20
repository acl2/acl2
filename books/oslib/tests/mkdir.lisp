; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
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
(include-book "../ls")
(include-book "../mkdir")
(include-book "../rmtree")
(include-book "std/util/defconsts" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "misc/assert" :dir :system)

(define basic-mkdir-test ((new-dir-name stringp) &key (state 'state))
  :returns (state state-p1 :hyp (state-p1 state))
  (b* (((mv errp orig-dirs state) (ls-subdirs "."))
       ((when errp)
        (raise "Error listing new subdirectories.")
        state)
       ((mv okp state) (mkdir new-dir-name))
       ((unless okp)
        (raise "Error making directory ~x0." new-dir-name)
        state)
       ((mv errp new-dirs state) (ls-subdirs "."))
       ((when errp)
        (raise "Error listing new subdirectories.")
        state)
       ((unless (equal (set::mergesort new-dirs)
                       (set::mergesort (cons new-dir-name orig-dirs))))
        (cw "Prev dirs: ~x0." orig-dirs)
        (cw "New dirs: ~x0." new-dirs)
        (raise "New directory ~x0 didn't get created." new-dir-name)
        state)
       ((mv okp state) (rmtree new-dir-name))
       ((unless okp)
        (raise "Error removing directory ~x0." new-dir-name)
        state)
       ((mv errp new-dirs state) (ls-subdirs "."))
       ((when errp)
        (raise "Error listing new subdirectories.")
        state)
       ((unless (equal (set::mergesort orig-dirs)
                       (set::mergesort new-dirs)))
        (cw "Prev dirs: ~x0." orig-dirs)
        (cw "New dirs: ~x0." new-dirs)
        (raise "New directory didn't get deleted?")
        state))
    state))

(defconsts state (basic-mkdir-test "tmpdir1"))
(defconsts state (basic-mkdir-test "tmpdir2"))
(defconsts state (basic-mkdir-test "tmpdir3"))



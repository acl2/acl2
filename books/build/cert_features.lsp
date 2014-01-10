; cert.pl build system
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>
;
; NOTE: This file is not part of the standard ACL2 books build process; it is
; part of an experimental build system.  The ACL2 developers do not maintain
; this file.

(in-package "ACL2")

(mv-let (channel state)
  (open-output-channel "Makefile-features" :character state)
  (if (not channel)
      (progn$
       (er hard? '|Makefile-features| "Error opening Makefile-features?")
       state)
    (let* ((state (princ$ #+hons "ACL2_HAS_HONS := 1"
                          #-hons "ACL2_HAS_HONS := "
                          channel state))
           (state (newline channel state))
           (state (princ$ #-(and gcl (not ansi-cl)) "ACL2_HAS_ANSI := 1"
                          #+(and gcl (not ansi-cl)) "ACL2_HAS_ANSI := "
                          channel state))
           (state (newline channel state))
           (state (princ$ #+acl2-par "ACL2_HAS_PARALLEL := 1"
                          #-acl2-par "ACL2_HAS_PARALLEL := "
                          channel state))
           (state (newline channel state))
           (state (princ$ #+non-standard-analysis "ACL2_HAS_REALS := 1"
                          #-non-standard-analysis "ACL2_HAS_REALS := "
                          channel state))
           (state (newline channel state))
           (state (princ$ "ACL2_COMP_EXT := " channel state))
           (state (princ$ (@ compiled-file-extension) channel state))
           (state (newline channel state))
           (state (princ$ "ACL2_HOST_LISP := " channel state))
           (state (princ$ (symbol-name (@ host-lisp)) channel state))
           (state (newline channel state))
           (state (close-output-channel channel state)))
      state)))

(good-bye 0)

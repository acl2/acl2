; ACL2 Parser for Java
; Copyright (C) 2013 Battelle Memorial Institute
;
; Contact:
;  David Rager, ragerdl@cs.utexas.edu
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
; Original author: David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")

(include-book "std/io/read-file-characters" :dir :system)
(include-book "std/util/define" :dir :system)

(define read-file-characters-no-error ((filename stringp)
                                      (state state-p))
  :returns (mv (characters character-listp :hyp :fguard)
               (state state-p :hyp :fguard))
  (mv-let (data state)
    (read-file-characters filename state)
    (mv (if (stringp data)
            (prog2$ (er hard? 'read-file-characters-no-error
                        data)
                    nil)
          data)
        state)))

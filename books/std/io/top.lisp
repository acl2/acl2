; Standard IO Library
; Portions are Copyright (C) 2008-2013 Centaur Technology
; Portions are Copyright (C) 2004-2006 by Jared Davis
; See individual books for details
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

(in-package "ACL2")
(include-book "base")
; (include-book "close-input-channel") ; stubbed out
(include-book "combine")
(include-book "nthcdr-bytes")
; (include-book "open-input-channel")  ; stubbed out
; (include-book "open-input-channels") ; unnecessary, I think
; (include-book "peek-char") ; stubbed out
; (include-book "read-byte") ; stubbed out
; (include-book "read-char") ; stubbed out
(include-book "read-file-bytes")
; (include-book "read-file-characters-no-error") ; omitted due to weird license stuff
(include-book "read-file-characters") 
(include-book "read-file-lines")
(include-book "read-file-objects")
(include-book "read-ints")
; (include-book "read-object") ; stubbed out
(include-book "signed-byte-listp")
(include-book "take-bytes")
(include-book "unsigned-byte-listp")


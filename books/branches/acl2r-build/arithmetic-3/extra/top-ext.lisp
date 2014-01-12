; Arithmetic-3 Extensions
; Copyright (C) 2006 Alex Spiridonov
;
; This program is free software; you can redistribute it and/ormodify it under
; the terms of the GNU General Public Licenseas published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version. This program is distributed in the hope that it will be useful, but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.You should have received a copy of the GNU General Public License along
; with this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA."

; Contributed by Alex Spiridonov, with helpful consulting from Robert Krug.

(in-package "ACL2")

(include-book "arithmetic-3/bind-free/top" :dir :system)
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)
(include-book "ext")

(add-default-hints! '((nonlinearp-default-hint stable-under-simplificationp 
                                               hist pspv)))

(in-theory (enable strong-expt-type-prescription-rules))

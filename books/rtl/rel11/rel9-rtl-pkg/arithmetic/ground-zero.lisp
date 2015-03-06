; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")
;includes changes to the default theory (mostly disabling built-in functions)

(in-theory (disable aref1))
(in-theory (disable aset1))
(in-theory (disable aref2))
(in-theory (disable aset2))
(in-theory (disable floor))
(in-theory (disable truncate))
(in-theory (disable mod))
(in-theory (disable rem))
(in-theory (disable expt))
(in-theory (disable ash))
(in-theory (disable acl2::binary-logand))
(in-theory (disable acl2::binary-logior))
(in-theory (disable acl2::binary-logxor))
(in-theory (disable acl2::binary-logeqv))
(in-theory (disable logorc1))
(in-theory (disable lognot))
(in-theory (disable evenp)) ;new
(in-theory (disable oddp)) ;new
(in-theory (disable nonnegative-integer-quotient)) ;new
;abs?


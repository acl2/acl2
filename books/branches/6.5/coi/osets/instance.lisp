#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
#|

   Fully Ordered Finite Sets, Version 0.9
   Copyright (C) 2003, 2004 by Jared Davis <jared@cs.utexas.edu>

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public Lic-
   ense along with this program; if not, write to the Free Soft-
   ware Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.



  instance.lisp

    This is a system for dynamically instantiating ACL2 "theories"
    (which are represented as constants) to create new, concrete
    "theories".

|#

(in-package "INSTANCE")

; [Jared] 2014-02-10: changed this book to just be a wrapper for the one in the
; std/osets library, which was identical modulo whitespace and comments.

; cert_param: (reloc_stub)
(include-book "std/osets/instance" :dir :system)

; ACL2 String Library
; Copyright (C) 2009 Centaur Technology
; Contact: jared@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "STR")

(defdoc Str
":Doc-Section Str
ACL2 String Library~/

This is a rudimentary string library for ACL2.  The functions here are all in
logic mode, with verified guards.  Effort has been spent to make them both
reasonably efficient and relatively straightforward to reason about.  Note that
since we make extensive use of MBE, you will need to verify your own functions'
guards in order to get good performance out of most library functions.

LOADING, DOCUMENTATION.

Ordinarily, to use the library one should run
~bv[]
(include-book \"str/top\" :dir :system)
~ev[]
The documentation is then available by writing ~c[:doc STR::str].  All of the
library's functions are found in the STR package, so you will need to do one of
the following.

  1. Type STR:: before the names of the functions,  OR

  2. Import STR::*exports* into your own package, OR

  3. Additionally load a set of ACL2-package macros which are aliases for the
     functions in the STR package.  To do this, run:
      ~c[(include-book \"str/abbrevs\" :dir :system)]

LIBRARY FUNCTIONS.

There are probably many things to add.  For now, here are the functions which
are available.

~/

LICENSE.

This program is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version.  This program is distributed in the hope that it will be useful but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
more details.  You should have received a copy of the GNU General Public
License along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.")

  
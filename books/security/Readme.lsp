((:FILES "
.:
Makefile
Readme.lsp
jfkr

./des:
Makefile
des.lisp
des-test.lisp

./jfkr:
MakeFile
cert.acl2
demo.lsp
diffie-helman.lisp
encryption.lisp
jfkr.lisp
package.lsp
random.lisp

./suite-b:
Makefile
sha-2.lisp

./util:
Makefile
byte-operations.lisp

")

 (:TITLE    "A gathering point for ACL2 books that model security protocols")

 (:AUTHOR/S "Soumava Ghosh, David L. Rager")

 (:KEYWORDS "jfkr" "security" "sha-2" "des" "strings-to-bits")

 (:ABSTRACT
"While theorem proving is considered by many of us to be related to
security, the goal of the books in this directory is to share libraries
that specifically analyze security protocols and related components.

Note that there are no Readme.lsp files for the subdirectories since the
subdirectories are captured by this Readme.lsp")

 (:PERMISSION
"For the jfkr directory:

Copyright (C) 2008 University of Texas at Austin
for files not explicitly copyrighted otherwise

This program is free software; you can redistribute it and/or modify
it under the terms of Version 2 of the GNU General Public License as
published by the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301, USA.

For the util, des, and suite-b directories:

Copyright (c) 2012, Soumava Ghosh
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the The University of Texas at Austin nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS 'AS IS' AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL SOUMAVA GHOSH BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
"))
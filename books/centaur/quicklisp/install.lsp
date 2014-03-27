; Centaur Books -- Quicklisp installer
; Copyright (C) 2008-2014 Centaur Technology
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

; This just does the initial quicklisp install.  It should get run when the
; Makefile tries to build setup.lisp

(make-event
 (let ((cbd (cbd)))
   `(defconst *cbd* ',cbd)))

;; Horrible junk to try to get ASDF not to put its stuff here, in the
;; quicklisp/asdf-home directory, rather than in the user's home directory in
;; places like ~/.cache and ~/.config.
(setenv$ "XDG_CONFIG_HOME" (concatenate 'string *cbd* "asdf-home/config"))
(setenv$ "XDG_DATA_HOME"   (concatenate 'string *cbd* "asdf-home/data"))
(setenv$ "XDG_CACHE_HOME"  (concatenate 'string *cbd* "asdf-home/cache"))

:q
(in-package "CL-USER")
(load "quicklisp.lsp")

(quicklisp-quickstart:install :path (concatenate 'string acl2::*cbd* "inst"))
(setq ql-util::*do-not-prompt* t)
(ql-dist:install-dist
 "http://beta.quicklisp.org/dist/quicklisp/2014-01-13/distinfo.txt"
 :replace t)

(quit)

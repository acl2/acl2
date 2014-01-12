; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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


; fmt-to-str.lisp -- alternative to fmt-to-string with narrower margins
; and downcased symbols

(in-package "XDOC")
(include-book "tools/bstar" :dir :system)
(set-state-ok t)
(program)

(defun fmt-to-str-aux (string alist base-pkg state)
  ;; Use ACL2's fancy new string-printing stuff to do pretty-printing
  (b* ((hard-right-margin   (f-get-global 'acl2::fmt-hard-right-margin state))
       (soft-right-margin   (f-get-global 'acl2::fmt-soft-right-margin state))
       (print-case          (f-get-global 'acl2::print-case state))
       (pkg                 (current-package state))
       (base-pkg-name       (symbol-package-name base-pkg))
       ((mv er ?val state)  (acl2::in-package-fn base-pkg-name state))
       ((when er)
        (er hard? 'fmt-to-str-aux "Error switching to package ~x0" base-pkg-name)
        (mv "" state))
       (state               (set-fmt-hard-right-margin 68 state))
       (state               (set-fmt-soft-right-margin 62 state))
       (state               (set-print-case :downcase state))
       ((mv channel state)  (open-output-channel :string :character state))
       ((mv ?col state)     (fmt1 string alist 0 channel state nil))
       ((mv er1 str state)  (get-output-stream-string$ channel state))
       ((mv er2 ?val state) (acl2::in-package-fn pkg state))
       (state               (set-fmt-hard-right-margin hard-right-margin state))
       (state               (set-fmt-soft-right-margin soft-right-margin state))
       (state               (set-print-case print-case state))
       ((when er1)
        (er hard? 'fmt-to-str-aux "Error with get-output-stream-string$?")
        (mv "" state))
       ((when er2)
        (er hard? 'fmt-to-str-aux "Error switching back to package ~x0" pkg)
        (mv "" state)))
    (mv str state)))

(defun fmt-to-str (x base-pkg state)
  ;; Basic formatting of sexprs, no encoding or autolinking
  (fmt-to-str-aux "~x0" (list (cons #\0 x)) base-pkg state))

(defun simple-html-encode-str (x n xl acc)

; Revappend the HTML encoding of X (e.g., & --> &amp;) onto ACC.

  (b* (((when (int= n xl))
        acc)
       (char1 (char x n))
       (acc   (case char1
                (#\< (list* #\; #\t #\l #\& acc))         ;; "&lt;" (in reverse)
                (#\> (list* #\; #\t #\g #\& acc))         ;; "&gt;"
                (#\& (list* #\; #\p #\m #\a #\& acc))     ;; "&amp;"
                (#\" (list* #\; #\t #\o #\u #\q #\& acc)) ;; "&quot;"
                (t   (cons char1 acc)))))
    (simple-html-encode-str x (+ 1 n) xl acc)))

(defun fmt-and-encode-to-acc-aux (string alist base-pkg state acc)
  ;; Basic formatting with automatic HTML encoding
  (b* (((mv str state) (fmt-to-str-aux string alist base-pkg state))
       (acc (simple-html-encode-str str 0 (length str) acc)))
    (mv acc state)))

(defun fmt-and-encode-to-acc (x base-pkg state acc)
  ;; Basic encoding of sexprs with no autolinking.
  (fmt-and-encode-to-acc-aux "~x0" (list (cons #\0 x)) base-pkg state acc))

; Converter From ACL2 System Documentation to Text
; Copyright (C) 2013 Centaur Technology
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
; 10/29/2013: Mods made by Matt Kaufmann to support Emacs-based ACL2-Doc browser

(in-package "XDOC")
(include-book "xdoc/display" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(set-state-ok t)
(program)

(include-book "acl2-doc-wrap")

(defun render-topic (x all-topics state)
  ;; Adapted from display-topic
  (b* ((name (cdr (assoc :name x)))
       (parents (cdr (assoc :parents x)))
       ((mv text state) (preprocess-topic
                         (acons :parents nil x) ;; horrible hack
                         all-topics nil nil state))
       ((mv err tokens) (parse-xml text))

       ((when err)
        (cw "Error rendering xdoc topic ~x0:~%~%" name)
        (b* ((state (princ$ err *standard-co* state))
             (state (newline *standard-co* state))
             (state (newline *standard-co* state)))
          (er hard? 'make-topic-text "Failed to process topic ~x0.~%" name)
          (mv nil state)))

       (merged-tokens (reverse (merge-text tokens nil 0)))
       (acc (tokens-to-terminal merged-tokens 70 nil nil nil))
       (terminal (str::trim (str::rchars-to-string acc))))

; Originally the first value returned was (cons name terminal).  But we prefer
; to avoid the "." in the output file, to make its viewing more pleasant.  If
; we decide to associate additional information with name, then we may have a
; more convincing reason to make this change.

    (mv (list name parents terminal) state)))

(defun render-topics (x all-topics state)
  (b* (((when (atom x))
        (mv nil state))
       ((mv first state) (render-topic (car x) all-topics state))
       ((mv rest state) (render-topics (cdr x) all-topics state)))
    (mv (cons first rest) state)))

(defun set-current-package-state (pkg state)
  (mv-let (erp val state)
          (acl2::set-current-package pkg state)
          (declare (ignore val))
          (assert$ (null erp)
                   state)))

(defun split-acl2-topics (alist acl2-topics acl2-pc-topics other-topics)

; Added by Matt K.  It seems good to me for there to be an intuitive sense of
; the order of topics when one is searching using the Emacs interface to the
; documentation, specifically, the "," key.  So we put the "ACL2-PC" package
; topics at the end, since to me they seem less likely to be what one is
; searching for.

  (cond ((endp alist)
         (append (acl2::merge-sort-symbol-alistp acl2-topics)
                 (acl2::merge-sort-symbol-alistp acl2-pc-topics)
                 (acl2::merge-sort-symbol-alistp other-topics)))
        ((eq (intern (symbol-name (caar alist)) "ACL2")
             (caar alist))
         (split-acl2-topics (cdr alist)
                            (cons (car alist) acl2-topics)
                            acl2-pc-topics
                            other-topics))
        ((equal (symbol-package-name (caar alist)) "ACL2-PC")
         (split-acl2-topics (cdr alist)
                            acl2-topics
                            (cons (car alist) acl2-pc-topics)
                            other-topics))
        (t
         (split-acl2-topics (cdr alist)
                            acl2-topics
                            acl2-pc-topics
                            (cons (car alist) other-topics)))))

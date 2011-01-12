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

(in-package "ACL2") ;; So the acl2 topic comes from the acl2 package.
(include-book "write-acl2-xdoc")
(program)

; Initial import of acl2 system documentation.  We do this before including any
; books other than the basic portcullis, because we don't want any libraries
; loaded when we import the system-level documentation.
;
; One other minor fixup: In ACL2, a top-level topic has a parent of itself.  We
; change all such top-level topics so that they have a parent of acl2::acl2.

#!XDOC
(progn
  (defun remove-alist-key (key x)
    (cond ((atom x)
           nil)
          ((atom (car x))
           (remove-alist-key key (cdr x)))
          ((equal (caar x) key)
           (remove-alist-key key (cdr x)))
          (t
           (cons (car x) (remove-alist-key key (cdr x))))))

  (defun change-self-parent-to-acl2 (topic)
    (let ((name    (cdr (assoc :name topic)))
          (parents (cdr (assoc :parents topic))))
      (if (member name parents)
          (acons :parents
                 (cons 'acl2::acl2 (remove-equal name parents))
                 (remove-alist-key :parents topic))
        topic)))

  (defun change-self-parents-to-acl2 (topics)
    (if (atom topics)
        nil
      (cons (change-self-parent-to-acl2 (car topics))
            (change-self-parents-to-acl2 (cdr topics)))))

  (defun all-topic-names (topics)
    (if (atom topics)
        nil
      (cons (cdr (assoc :name (car topics)))
            (all-topic-names (cdr topics)))))

  (defun remove-topics-by-name (topics names)
    (cond ((atom topics)
           nil)
          ((member (cdr (assoc :name (car topics))) names)
           (remove-topics-by-name (cdr topics) names))
          (t
           (cons (car topics) (remove-topics-by-name (cdr topics) names)))))

  (make-event
   (mv-let (er val state)
     (time$ (acl2::write-xdoc-alist)
            :msg "; Importing ground-zero acl2 :doc topics: ~st sec, ~sa bytes~%"
            :mintime 1)
     (declare (ignore er val))
     (let* ((topics (acl2::f-get-global 'acl2::xdoc-alist state))
            (topics (change-self-parents-to-acl2 topics))
            (names  (all-topic-names topics)))
       (value `(progn
                 (defconst *acl2-ground-zero-names* ',names)
                 (defconst *acl2-ground-zero-topics* ',topics)))))))

(include-book "base")

#!XDOC
;; Actually install the ground-zero topics
(table xdoc 'doc (append *acl2-ground-zero-topics* (get-xdoc-table world)))

(defxdoc acl2
  :short "Documentation for the ACL2 Theorem Prover."
  :long "<p>This is just a parent topic for all built-in <see topic=\"@(url
documentation)\">ACL2 documentation</see> that is written in the classic @(see
doc-string) format.</p>")

#!XDOC
(defmacro import-acl2doc ()
  ;; This is for refreshing the documentation to reflect topics documented in
  ;; libraries.  We throw away any ACL2-system topics that we've already had
  ;; added to the xdoc table.
  `(make-event
    (mv-let (er val state)
      (time$ (acl2::write-xdoc-alist)
             :msg "; Importing acl2 :doc topics: ~st sec, ~sa bytes~%"
             :mintime 1)
      (declare (ignore er val))
      (let* ((topics (acl2::f-get-global 'acl2::xdoc-alist state))
             (topics (time$ (remove-topics-by-name topics *acl2-ground-zero-names*))))
        (value `(table xdoc 'doc
                       (append ',topics (get-xdoc-table world))))))))


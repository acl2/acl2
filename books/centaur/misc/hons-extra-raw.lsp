; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(defmacro with-fast-alist-raw (alist form)
  (let ((alist-was-fast-p (gensym))
        (alist-var (if (legal-variablep alist)
                       alist
                     (gensym))))
    `(b* ((- (hl-maybe-initialize-default-hs))
          ;; If alist isn't a variable, then depend on it being a computation
          ;; that returns the same (eq) object each time, and that object can
          ;; be turned into an (eq) fast alist, i.e. its keys are normed.  If
          ;; not, then the user may not find their alist to be fast during the
          ;; execution of form, but we'll still correctly free it.
          (,alist-var ,alist)
          (,alist-was-fast-p
           (let ((slot (hl-faltable-general-lookup ,alist-var (hl-hspace-faltable *default-hs*))))
             (if (hl-falslot-key slot)
                 t
               nil)))
          (,alist-var (if ,alist-was-fast-p
                          ,alist-var
                        (make-fast-alist ,alist-var))))
       (our-multiple-value-prog1
        ,form
        (if ,alist-was-fast-p
            nil
          (fast-alist-free ,alist-var))))))

(defmacro with-stolen-alist-raw (alist form)
  (let ((alist-was-fast-p (gensym))
        (alist-var (if (legal-variablep alist)
                       alist
                     (gensym))))
    `(b* ((- (hl-maybe-initialize-default-hs))
          ;; If alist isn't a variable, then depend on it being a computation
          ;; that returns the same (eq) object each time, and that object can
          ;; be turned into an (eq) fast alist, i.e. its keys are normed.  If
          ;; not, then the user may not find their alist to be fast during the
          ;; execution of form, but we'll still correctly free it.
          (,alist-var ,alist)
          (,alist-was-fast-p
           (let ((slot (hl-faltable-general-lookup ,alist-var (hl-hspace-faltable *default-hs*))))
             (if (hl-falslot-key slot)
                 t
               nil)))
          (,alist-var (if ,alist-was-fast-p
                          ,alist-var
                        (make-fast-alist ,alist-var))))
       (our-multiple-value-prog1
        ,form
        (if ,alist-was-fast-p
            (make-fast-alist ,alist-var)
          (fast-alist-free ,alist-var))))))


; ACL2 Theory Linter
; Copyright (C) 2013 Kookamara LLC
;
; Contact:
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759
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
; Original authors: Jared Davis <jared@kookamara.com>

(in-package "STD")
(include-book "da-base")
(program)

(defxdoc defaggrify-defrec
  :parents (defaggregate)
  :short "Add @(see defaggregate)-style emulation for @('defrec') records."

  :long "<p>The @('defrec') macro is an undocumented utility which is used
within the ACL2 theorem prover to introduce structures.  Although many of the
details are different, it is in many ways like @(see defaggregate).</p>

<p>@(call defaggregate-defrec-emulation) is a macro that automatically adds
@('defaggregate')-style accessors and @(see b*) binders that work on
@('defrec') structures.</p>

<p>Typical usage is, e.g.,:</p>

@({
     (in-package \"ACL2\")
     (std::defaggregate-defrec-emulation rewrite-rule)
     (std::defaggregate-defrec-emulation def-body)
     ...
})

<p>We may eventually extend this to include additional @('defaggregate')-style
features such as @('make-') and @('change-') macros.</p>")

(defun flatten-defrec-fields (x)
  ;; Flatten a defrec field layout (which can be an arbitrary shaped cons tree)
  ;; into an ordinary list.
  (if (atom x)
      (and x (list x))
    (append (flatten-defrec-fields (car x))
            (flatten-defrec-fields (cdr x)))))

(defun look-up-defrec-fields (rec world)
  ;; Horrible awful thing.  The fields for a defrec aren't saved anywhere
  ;; explicitly, but we can look them up in the body of the MAKE function.
  ;; See the function MAKE-RECORD-MAKER in the acl2 sources.
  (b* ((maker (acl2::record-maker-function-name rec))
       (body  (getprop maker 'acl2::macro-body nil 'acl2::current-acl2-world world))
       ((unless body)
        (er hard? 'look-up-defrec-field-layout
            "Can't find macro-body for maker ~x0 of defrec ~x1.  is ~x1 even ~
             a defrec?" maker rec))
       (quoted-layout (third body))
       ((unless (quotep quoted-layout))
        (er hard? 'look-up-defrec-field-layout
            "Sanity check failed, field layout of ~x0 is not a quotep?" rec)))
    (flatten-defrec-fields
     (acl2::unquote quoted-layout))))

(defun da-accessor-for-defrec-field (rec field)
  ;; Create a defaggregate-style accessor foo->bar for field bar of defrec foo
  (let ((weak-rec-p (intern$ (concatenate 'string "WEAK-" (symbol-name rec) "-P")
                             "ACL2")))
    `(defun-inline ,(std::da-accessor-name rec field) (x)
       (declare (xargs :guard (,weak-rec-p x)))
       (acl2::access ,rec x ,(intern$ (symbol-name field) "KEYWORD")))))

(defun da-accessors-for-defrec-fields (rec fields)
  (if (atom fields)
      nil
    (cons (da-accessor-for-defrec-field rec (car fields))
          (da-accessors-for-defrec-fields rec (cdr fields)))))

(defun da-defrec-emulation-fn (rec world)
  (let ((fields (look-up-defrec-fields rec world)))
    `(encapsulate nil
       (logic)
       ,@(da-accessors-for-defrec-fields rec fields)
       ,(std::da-make-binder rec fields))))

(defmacro defaggrify-defrec (rec)
  `(make-event
    (b* ((world (w state)))
      (value (da-defrec-emulation-fn ',rec world)))))

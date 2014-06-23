; VL Verilog Toolkit
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

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection context
  :parents (mlib)
  :short "Tools for working with \"arbitrary\" module elements.  These
functions are often useful, e.g., when writing linter checks, or when writing
warning messages that need to explain where an error occurs.")

(local (xdoc::set-default-parents context))

(deftranssum vl-modelement
  :short "Recognizer for an arbitrary module element."

  :long "<p>It is sometimes useful to be able to deal with module elements of
arbitrary types.  For instance, we often use this in error messages, along with
@(see vl-context-p), to describe where expressions occur.  We also use it in
our @(see parser), where before module formation, the module elements are
initially kept in a big, mixed list.</p>"
  (vl-port
   vl-portdecl
   vl-assign
   vl-netdecl
   vl-vardecl
   vl-eventdecl
   vl-paramdecl
   vl-fundecl
   vl-taskdecl
   vl-modinst
   vl-gateinst
   vl-always
   vl-initial))

(fty::deflist vl-modelementlist
  :elt-type vl-modelement-p)

(deflist vl-modelementlist-p (x)
  (vl-modelement-p x)
  :elementp-of-nil nil
  :rest
  ((defthm vl-modelementlist-p-when-vl-portlist-p
     (implies (vl-portlist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-portdecllist-p
     (implies (vl-portdecllist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-assignlist-p
     (implies (vl-assignlist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-netdecllist-p
     (implies (vl-netdecllist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-vardecllist-p
     (implies (vl-vardecllist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-eventdecllist-p
     (implies (vl-eventdecllist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-paramdecllist-p
     (implies (vl-paramdecllist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-fundecllist-p
     (implies (vl-fundecllist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-taskdecllist-p
     (implies (vl-taskdecllist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-modinstlist-p
     (implies (vl-modinstlist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-gateinstlist-p
     (implies (vl-gateinstlist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-alwayslist-p
     (implies (vl-alwayslist-p x)
              (vl-modelementlist-p x)))

   (defthm vl-modelementlist-p-when-vl-initiallist-p
     (implies (vl-initiallist-p x)
              (vl-modelementlist-p x)))))


(define vl-modelement-loc ((x vl-modelement-p))
  :short "Get the location of any @(see vl-modelement-p)."
  :returns (loc vl-location-p
                :hints(("Goal" :in-theory (enable vl-modelement-fix))))
  (b* ((x (vl-modelement-fix x)))
    (case (tag x)
      (:vl-port      (vl-port->loc x))
      (:vl-portdecl  (vl-portdecl->loc x))
      (:vl-assign    (vl-assign->loc x))
      (:vl-netdecl   (vl-netdecl->loc x))
      (:vl-vardecl   (vl-vardecl->loc x))
      (:vl-eventdecl (vl-eventdecl->loc x))
      (:vl-paramdecl (vl-paramdecl->loc x))
      (:vl-fundecl   (vl-fundecl->loc x))
      (:vl-taskdecl  (vl-taskdecl->loc x))
      (:vl-modinst   (vl-modinst->loc x))
      (:vl-gateinst  (vl-gateinst->loc x))
      (:vl-always    (vl-always->loc x))
      (:vl-initial   (vl-initial->loc x)))))



(define vl-sort-modelements
  ((x vl-modelementlist-p)
   (ports vl-portlist-p)
   (portdecls vl-portdecllist-p)
   (assigns vl-assignlist-p)
   (netdecls vl-netdecllist-p)
   (vardecls vl-vardecllist-p)
   (eventdecls vl-eventdecllist-p)
   (paramdecls vl-paramdecllist-p)
   (fundecls vl-fundecllist-p)
   (taskdecls vl-taskdecllist-p)
   (modinsts vl-modinstlist-p)
   (gateinsts vl-gateinstlist-p)
   (alwayses vl-alwayslist-p)
   (initials vl-initiallist-p))
  :returns (mv (ports vl-portlist-p)
               (portdecls vl-portdecllist-p)
               (assigns vl-assignlist-p)
               (netdecls vl-netdecllist-p)
               (vardecls vl-vardecllist-p)
               (eventdecls vl-eventdecllist-p)
               (paramdecls vl-paramdecllist-p)
               (fundecls vl-fundecllist-p)
               (taskdecls vl-taskdecllist-p)
               (modinsts vl-modinstlist-p)
               (gateinsts vl-gateinstlist-p)
               (alwayses vl-alwayslist-p)
               (initials vl-initiallist-p))
  (b* (((when (atom x))
        (mv (rev (vl-portlist-fix ports))
            (rev (vl-portdecllist-fix portdecls))
            (rev (vl-assignlist-fix assigns))
            (rev (vl-netdecllist-fix netdecls))
            (rev (vl-vardecllist-fix vardecls))
            (rev (vl-eventdecllist-fix eventdecls))
            (rev (vl-paramdecllist-fix paramdecls))
            (rev (vl-fundecllist-fix fundecls))
            (rev (vl-taskdecllist-fix taskdecls))
            (rev (vl-modinstlist-fix modinsts))
            (rev (vl-gateinstlist-fix gateinsts))
            (rev (vl-alwayslist-fix alwayses))
            (rev (vl-initiallist-fix initials))))
       (x1  (vl-modelement-fix (car x)))
       (tag (tag x1)))
    (vl-sort-modelements (cdr x)
                         (if (eq tag :vl-port)      (cons x1 ports)      ports)
                         (if (eq tag :vl-portdecl)  (cons x1 portdecls)  portdecls)
                         (if (eq tag :vl-assign)    (cons x1 assigns)    assigns)
                         (if (eq tag :vl-netdecl)   (cons x1 netdecls)   netdecls)
                         (if (eq tag :vl-vardecl)   (cons x1 vardecls)   vardecls)
                         (if (eq tag :vl-eventdecl) (cons x1 eventdecls) eventdecls)
                         (if (eq tag :vl-paramdecl) (cons x1 paramdecls) paramdecls)
                         (if (eq tag :vl-fundecl)   (cons x1 fundecls)   fundecls)
                         (if (eq tag :vl-taskdecl)  (cons x1 taskdecls)  taskdecls)
                         (if (eq tag :vl-modinst)   (cons x1 modinsts)   modinsts)
                         (if (eq tag :vl-gateinst)  (cons x1 gateinsts)  gateinsts)
                         (if (eq tag :vl-always)    (cons x1 alwayses)   alwayses)
                         (if (eq tag :vl-initial)   (cons x1 initials)   initials)))
  :prepwork
  ((local (in-theory (disable
                      ;; just a speed hint
                      double-containment
                      set::nonempty-means-set
                      acl2::consp-under-iff-when-true-listp
                      acl2::consp-by-len
                      acl2::true-listp-when-character-listp
                      acl2::true-listp-when-atom
                      set::sets-are-true-lists
                      consp-when-member-equal-of-cons-listp
                      consp-when-member-equal-of-cons-listp
                      acl2::rev-when-not-consp
                      default-car
                      default-cdr
                      pick-a-point-subset-strategy
                      vl-modelement-p-when-member-equal-of-vl-modelementlist-p
                      vl-portlist-p-when-subsetp-equal
                      vl-initiallist-p-when-subsetp-equal
                      vl-assignlist-p-when-subsetp-equal
                      vl-alwayslist-p-when-subsetp-equal
                      vl-vardecllist-p-when-subsetp-equal
                      vl-paramdecllist-p-when-subsetp-equal
                      vl-netdecllist-p-when-subsetp-equal
                      vl-modinstlist-p-when-subsetp-equal
                      vl-gateinstlist-p-when-subsetp-equal
                      vl-fundecllist-p-when-subsetp-equal
                      vl-taskdecllist-p-when-subsetp-equal
                      vl-eventdecllist-p-when-subsetp-equal
                      vl-portdecllist-p-when-subsetp-equal
                      vl-modelementlist-p-when-vl-portlist-p
                      vl-modelementlist-p-when-vl-initiallist-p
                      vl-modelementlist-p-when-vl-vardecllist-p
                      vl-modelementlist-p-when-vl-portdecllist-p
                      vl-modelementlist-p-when-vl-netdecllist-p
                      vl-modelementlist-p-when-vl-modinstlist-p
                      vl-modelementlist-p-when-vl-gateinstlist-p
                      vl-modelementlist-p-when-vl-fundecllist-p
                      vl-modelementlist-p-when-vl-taskdecllist-p
                      vl-modelementlist-p-when-vl-eventdecllist-p
                      vl-modelementlist-p-when-vl-assignlist-p
                      vl-modelementlist-p-when-vl-alwayslist-p
                      (:rules-of-class :type-prescription :here)
                      (:ruleset tag-reasoning)
                      )))))

(defprod vl-context
  :short "Description of where an expression occurs."
  :tag :vl-context
  :layout :tree
  ((mod  stringp :rule-classes :type-prescription
         "The module where this module element was taken from.")
   (elem vl-modelement-p
         "Some element from the module.")))


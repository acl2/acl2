; VL Verilog Toolkit
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))


(defsection vl-modelement-p
  :parents (vl-context-p)
  :short "Recognizer for an arbitrary module element."

  :long "<p>It is sometimes useful to be able to deal with module elements of
arbitrary types.  For instance, we often use this in error messages, along with
@(see vl-context-p), to describe where expressions occur.  We also use it in
our @(see parser), where before module formation, the module elements are
initially kept in a big, mixed list.</p>"

  (defund vl-modelement-p (x)
    (declare (xargs :guard t))
    (mbe :logic (or (vl-port-p x)
                    (vl-portdecl-p x)
                    (vl-assign-p x)
                    (vl-netdecl-p x)
                    (vl-vardecl-p x)
                    (vl-regdecl-p x)
                    (vl-eventdecl-p x)
                    (vl-paramdecl-p x)
                    (vl-fundecl-p x)
                    (vl-taskdecl-p x)
                    (vl-modinst-p x)
                    (vl-gateinst-p x)
                    (vl-always-p x)
                    (vl-initial-p x))
         :exec (case (tag x)
                 (:vl-port      (vl-port-p x))
                 (:vl-portdecl  (vl-portdecl-p x))
                 (:vl-assign    (vl-assign-p x))
                 (:vl-netdecl   (vl-netdecl-p x))
                 (:vl-vardecl   (vl-vardecl-p x))
                 (:vl-regdecl   (vl-regdecl-p x))
                 (:vl-eventdecl (vl-eventdecl-p x))
                 (:vl-paramdecl (vl-paramdecl-p x))
                 (:vl-fundecl   (vl-fundecl-p x))
                 (:vl-taskdecl  (vl-taskdecl-p x))
                 (:vl-modinst   (vl-modinst-p x))
                 (:vl-gateinst  (vl-gateinst-p x))
                 (:vl-always    (vl-always-p x))
                 (:vl-initial   (vl-initial-p x)))))

  (local (in-theory (enable vl-modelement-p)))

  (defthm consp-when-vl-modelement-p
    (implies (vl-modelement-p x)
             (consp x))
    :rule-classes :compound-recognizer)

  (defthm vl-modelement-p-when-vl-port-p
    (implies (vl-port-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-portdecl-p
    (implies (vl-portdecl-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-assign-p
    (implies (vl-assign-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-netdecl-p
    (implies (vl-netdecl-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-vardecl-p
    (implies (vl-vardecl-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-regdecl-p
    (implies (vl-regdecl-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-eventdecl-p
    (implies (vl-eventdecl-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-paramdecl-p
    (implies (vl-paramdecl-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-fundecl-p
    (implies (vl-fundecl-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-taskdecl-p
    (implies (vl-taskdecl-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-modinst-p
    (implies (vl-modinst-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-gateinst-p
    (implies (vl-gateinst-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-always-p
    (implies (vl-always-p x)
             (vl-modelement-p x)))

  (defthm vl-modelement-p-when-vl-initial-p
    (implies (vl-initial-p x)
             (vl-modelement-p x)))


;; Note.  When I merged vl-moduleitem-p and vl-modelement-p, the moduleitem-p
;; rules had :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))) but these
;; rules did not.  If these rules turn out to be slow, consider adding that
;; back in.  Consider similar limits on the analagous rules for atomicstmts,
;; atomguts, etc.

  (defthm vl-port-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-port)
                  (vl-modelement-p x))
             (vl-port-p x)))

  (defthm vl-portdecl-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-portdecl)
                  (vl-modelement-p x))
             (vl-portdecl-p x)))

  (defthm vl-assign-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-assign)
                  (vl-modelement-p x))
             (vl-assign-p x)))

  (defthm vl-netdecl-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-netdecl)
                  (vl-modelement-p x))
             (vl-netdecl-p x)))

  (defthm vl-vardecl-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-vardecl)
                  (vl-modelement-p x))
             (vl-vardecl-p x)))

  (defthm vl-regdecl-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-regdecl)
                  (vl-modelement-p x))
             (vl-regdecl-p x)))

  (defthm vl-eventdecl-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-eventdecl)
                  (vl-modelement-p x))
             (vl-eventdecl-p x)))

  (defthm vl-paramdecl-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-paramdecl)
                  (vl-modelement-p x))
             (vl-paramdecl-p x)))

  (defthm vl-fundecl-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-fundecl)
                  (vl-modelement-p x))
             (vl-fundecl-p x)))

  (defthm vl-taskdecl-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-taskdecl)
                  (vl-modelement-p x))
             (vl-taskdecl-p x)))

  (defthm vl-modinst-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-modinst)
                  (vl-modelement-p x))
             (vl-modinst-p x)))

  (defthm vl-gateinst-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-gateinst)
                  (vl-modelement-p x))
             (vl-gateinst-p x)))

  (defthm vl-always-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-always)
                  (vl-modelement-p x))
             (vl-always-p x)))

  (defthm vl-initial-p-by-tag-when-vl-modelement-p
    (implies (and (equal (tag x) :vl-initial)
                  (vl-modelement-p x))
             (vl-initial-p x)))

  (defthm vl-modelement-p-when-invalid-tag
    (implies (and (not (equal (tag x) :vl-port))
                  (not (equal (tag x) :vl-portdecl))
                  (not (equal (tag x) :vl-assign))
                  (not (equal (tag x) :vl-netdecl))
                  (not (equal (tag x) :vl-vardecl))
                  (not (equal (tag x) :vl-regdecl))
                  (not (equal (tag x) :vl-eventdecl))
                  (not (equal (tag x) :vl-paramdecl))
                  (not (equal (tag x) :vl-fundecl))
                  (not (equal (tag x) :vl-taskdecl))
                  (not (equal (tag x) :vl-modinst))
                  (not (equal (tag x) :vl-gateinst))
                  (not (equal (tag x) :vl-always))
                  (not (equal (tag x) :vl-initial)))
             (equal (vl-modelement-p x)
                    nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))




(deflist vl-modelementlist-p (x)
  (vl-modelement-p x)
  :elementp-of-nil nil
  :parents (vl-modelement-p)
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

   (defthm vl-modelementlist-p-when-vl-regdecllist-p
     (implies (vl-regdecllist-p x)
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



(defsection vl-modelement-loc
  :parents (vl-modelement-p)
  :short "Get the location of any @(see vl-modelement-p)."

  (defund vl-modelement-loc (x)
    (declare (xargs :guard (vl-modelement-p x)))
    (case (tag x)
      (:vl-port      (vl-port->loc x))
      (:vl-portdecl  (vl-portdecl->loc x))
      (:vl-assign    (vl-assign->loc x))
      (:vl-netdecl   (vl-netdecl->loc x))
      (:vl-vardecl   (vl-vardecl->loc x))
      (:vl-regdecl   (vl-regdecl->loc x))
      (:vl-eventdecl (vl-eventdecl->loc x))
      (:vl-paramdecl (vl-paramdecl->loc x))
      (:vl-fundecl   (vl-fundecl->loc x))
      (:vl-taskdecl  (vl-taskdecl->loc x))
      (:vl-modinst   (vl-modinst->loc x))
      (:vl-gateinst  (vl-gateinst->loc x))
      (:vl-always    (vl-always->loc x))
      (:vl-initial   (vl-initial->loc x))
      (otherwise
       (prog2$ (er hard 'vl-modinst->loc "Impossible")
               *vl-fakeloc*))))

  (local (in-theory (enable vl-modelement-loc)))

  (defthm vl-location-p-of-vl-modelement-loc
    (implies (force (vl-modelement-p x))
             (vl-location-p (vl-modelement-loc x)))))



(defsection vl-sort-modelements

  (local (in-theory (disable
                     ;; just a speed hint
                     double-containment
                     sets::nonempty-means-set
                     consp-under-iff-when-true-listp
                     consp-by-len
                     true-listp-when-character-listp
                     true-listp-when-symbol-listp
                     true-listp-when-string-listp
                     true-listp-when-not-consp
                     sets::sets-are-true-lists
                     consp-when-member-equal-of-cons-listp
                     consp-when-member-equal-of-cons-listp
                     acl2::rev-when-not-consp
                     default-car
                     default-cdr
                     pick-a-point-subset-strategy
                     vl-modelement-p-when-member-equal-of-vl-modelementlist-p
                     vl-portlist-p-when-subsetp-equal
                     vl-initiallist-p-when-subsetp-equal
                     vl-regdecllist-p-when-subsetp-equal
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
                     vl-modelementlist-p-when-vl-regdecllist-p
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
                     )))

  (defund vl-sort-modelements (x ports portdecls assigns netdecls vardecls regdecls
                                 eventdecls paramdecls fundecls taskdecls
                                 modinsts gateinsts alwayses initials)
    (declare (xargs :guard (and (vl-modelementlist-p x)
                                (vl-portlist-p ports)
                                (vl-portdecllist-p portdecls)
                                (vl-assignlist-p assigns)
                                (vl-netdecllist-p netdecls)
                                (vl-vardecllist-p vardecls)
                                (vl-regdecllist-p regdecls)
                                (vl-eventdecllist-p eventdecls)
                                (vl-paramdecllist-p paramdecls)
                                (vl-fundecllist-p fundecls)
                                (vl-taskdecllist-p taskdecls)
                                (vl-modinstlist-p modinsts)
                                (vl-gateinstlist-p gateinsts)
                                (vl-alwayslist-p alwayses)
                                (vl-initiallist-p initials)
                                (true-listp ports)
                                (true-listp portdecls)
                                (true-listp assigns)
                                (true-listp netdecls)
                                (true-listp vardecls)
                                (true-listp regdecls)
                                (true-listp eventdecls)
                                (true-listp paramdecls)
                                (true-listp fundecls)
                                (true-listp taskdecls)
                                (true-listp modinsts)
                                (true-listp gateinsts)
                                (true-listp alwayses)
                                (true-listp initials))))
    (b* (((when (atom x))
          (mv (reverse ports)
              (reverse portdecls)
              (reverse assigns)
              (reverse netdecls)
              (reverse vardecls)
              (reverse regdecls)
              (reverse eventdecls)
              (reverse paramdecls)
              (reverse fundecls)
              (reverse taskdecls)
              (reverse modinsts)
              (reverse gateinsts)
              (reverse alwayses)
              (reverse initials)))
         (tag (tag (car x))))
      (vl-sort-modelements (cdr x)
                           (if (eq tag :vl-port)      (cons (car x) ports)      ports)
                           (if (eq tag :vl-portdecl)  (cons (car x) portdecls)  portdecls)
                           (if (eq tag :vl-assign)    (cons (car x) assigns)    assigns)
                           (if (eq tag :vl-netdecl)   (cons (car x) netdecls)   netdecls)
                           (if (eq tag :vl-vardecl)   (cons (car x) vardecls)   vardecls)
                           (if (eq tag :vl-regdecl)   (cons (car x) regdecls)   regdecls)
                           (if (eq tag :vl-eventdecl) (cons (car x) eventdecls) eventdecls)
                           (if (eq tag :vl-paramdecl) (cons (car x) paramdecls) paramdecls)
                           (if (eq tag :vl-fundecl)   (cons (car x) fundecls)   fundecls)
                           (if (eq tag :vl-taskdecl)  (cons (car x) taskdecls)  taskdecls)
                           (if (eq tag :vl-modinst)   (cons (car x) modinsts)   modinsts)
                           (if (eq tag :vl-gateinst)  (cons (car x) gateinsts)  gateinsts)
                           (if (eq tag :vl-always)    (cons (car x) alwayses)   alwayses)
                           (if (eq tag :vl-initial)   (cons (car x) initials)   initials)
                           )))

  (local (in-theory (enable vl-sort-modelements)))

  (defthm vl-sort-modelements-basics
    (implies (force (and (vl-portlist-p ports)
                         (vl-modelementlist-p x)
                         (vl-portdecllist-p portdecls)
                         (vl-assignlist-p assigns)
                         (vl-netdecllist-p netdecls)
                         (vl-vardecllist-p vardecls)
                         (vl-regdecllist-p regdecls)
                         (vl-eventdecllist-p eventdecls)
                         (vl-paramdecllist-p paramdecls)
                         (vl-fundecllist-p fundecls)
                         (vl-taskdecllist-p taskdecls)
                         (vl-modinstlist-p modinsts)
                         (vl-gateinstlist-p gateinsts)
                         (vl-alwayslist-p alwayses)
                         (vl-initiallist-p initials)
                         (true-listp ports)
                         (true-listp portdecls)
                         (true-listp assigns)
                         (true-listp netdecls)
                         (true-listp vardecls)
                         (true-listp regdecls)
                         (true-listp eventdecls)
                         (true-listp paramdecls)
                         (true-listp fundecls)
                         (true-listp taskdecls)
                         (true-listp modinsts)
                         (true-listp gateinsts)
                         (true-listp alwayses)
                         (true-listp initials)))
             (b* (((mv ports portdecls assigns netdecls
                       vardecls regdecls eventdecls
                       paramdecls fundecls taskdecls
                       modinsts gateinsts alwayses initials)
                   (vl-sort-modelements x ports portdecls assigns netdecls
                                        vardecls regdecls eventdecls
                                        paramdecls fundecls taskdecls
                                        modinsts gateinsts alwayses initials)))
               (and (vl-portlist-p ports)
                    (vl-portdecllist-p portdecls)
                    (vl-assignlist-p assigns)
                    (vl-netdecllist-p netdecls)
                    (vl-vardecllist-p vardecls)
                    (vl-regdecllist-p regdecls)
                    (vl-eventdecllist-p eventdecls)
                    (vl-paramdecllist-p paramdecls)
                    (vl-fundecllist-p fundecls)
                    (vl-taskdecllist-p taskdecls)
                    (vl-modinstlist-p modinsts)
                    (vl-gateinstlist-p gateinsts)
                    (vl-alwayslist-p alwayses)
                    (vl-initiallist-p initials))))
    :hints(("Goal" :induct t))))




(defaggregate vl-context
  (mod elem)
  :tag :vl-context
  :require ((stringp-of-vl-context->mod
             (stringp mod)
             :rule-classes :type-prescription)
            (vl-modelement-p-of-vl-context->elem
             (vl-modelement-p elem)))
  :parents (ctxexprs)
  :short "Description of where an expression occurs."
  :long "<p>The @('mod') field names the module where this expression was taken
from.</p>

<p>The @('elem') is a @(see vl-modelement-p) that describes more precisely
where the expression occurred in @('mod').</p>")

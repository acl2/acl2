; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "inject-comments") ;; BOZO for description->minloc, etc.
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc inject-warnings
  :parents (loader)
  :short "Mechanism for attaching @(see warnings) to particular modules or
other design elements."

  :long "<p>Warnings from the early stages of parsing (e.g., lexing and
preprocessing) are created well before we have any modules (or other kinds of
descriptions, e.g., interfaces) to attach them to.  By convention, we create
these warnings so that their first argument is the location.  When warnings
follow this convention, we can attempt to associate them with modules.</p>

<p>Note: we generally don't expect there to be too many warnings caused during
these stages of loading, so our injection code is not particularly
efficient.</p>")

(local (xdoc::set-default-parents inject-warnings))

(define vl-warning->loc ((x vl-warning-p))
  :short "Return the location of a warning, if it obeys the location convention."
  :returns (loc? (iff (vl-location-p loc?) loc?))
  (b* ((args (vl-warning->args x)))
    (and (consp args)
         (vl-location-p (car args))
         (car args))))

(define vl-filter-warnings-by-loc
  :short "Extract warnings that are between certain bounds."
  ((min      vl-location-p)
   (max      vl-location-p)
   (warnings vl-warninglist-p "Warnings to filter.")
   (between  vl-warninglist-p "Accumulator for warnings between min/max.")
   (beyond   vl-warninglist-p "Accumulator for warnings not between min/max."))
  :returns (mv (between vl-warninglist-p)
               (beyond  vl-warninglist-p))
  :measure (len warnings)
  (b* ((warnings (vl-warninglist-fix warnings))
       (between  (vl-warninglist-fix between))
       (beyond   (vl-warninglist-fix beyond))
       ((when (atom warnings))
        (mv between beyond))
       (warn1 (car warnings))
       (loc1  (vl-warning->loc warn1))
       ((when (and loc1
                   (vl-location-between-p loc1 min max)))
        (vl-filter-warnings-by-loc min max (cdr warnings)
                                   (cons warn1 between)
                                   beyond)))
    (vl-filter-warnings-by-loc min max (cdr warnings)
                               between
                               (cons warn1 beyond))))

(define vl-description-add-warnings
  :short "Add a list of warnings to a (suitable) description."
  ((x vl-description-p)
   (warnings vl-warninglist-p))
  :guard (vl-description-has-comments-p x)
  :returns (new-x vl-description-p)
  :prepwork ((local (in-theory (enable vl-description-has-comments-p))))
  (b* ((x        (vl-description-fix x))
       (warnings (vl-warninglist-fix warnings)))
    (case (tag x)
      (:vl-module    (change-vl-module    x :warnings (append-without-guard warnings (vl-module->warnings x))))
      (:vl-udp       (change-vl-udp       x :warnings (append-without-guard warnings (vl-udp->warnings x))))
      (:vl-interface (change-vl-interface x :warnings (append-without-guard warnings (vl-interface->warnings x))))
      (:vl-package   (change-vl-package   x :warnings (append-without-guard warnings (vl-package->warnings x))))
      (:vl-program   (change-vl-program   x :warnings (append-without-guard warnings (vl-program->warnings x))))
      (:vl-class     (change-vl-class     x :warnings (append-without-guard warnings (vl-class->warnings x))))
      (:vl-config    (change-vl-config    x :warnings (append-without-guard warnings (vl-config->warnings x))))
      (:vl-typedef   (change-vl-typedef   x :warnings (append-without-guard warnings (vl-typedef->warnings x))))
      (otherwise     (progn$ (impossible) x))))
  ///
  (defthm vl-description->name-of-vl-description-add-warnings
    (equal (vl-description->name (vl-description-add-warnings x warning))
           (vl-description->name x))
    :hints(("Goal" :in-theory (enable vl-description->name)))))

(define vl-description-inject-warnings
  :short "Extract and attach in-bounds warnings to a description."
  ((x        vl-description-p "Description to attach to.")
   (warnings vl-warninglist-p "List of early warnings."))
  :returns
  (mv (new-x    vl-description-p "Perhaps updated with some warnings.")
      (warnings vl-warninglist-p "Perhaps with some warnings removed."))
  (b* ((x        (vl-description-fix x))
       (warnings (vl-warninglist-fix warnings))

       ((when (atom warnings))
        ;; There are no warnings to attach, so there's nothing to do and we may
        ;; as well quit early.
        (mv x warnings))

       ((unless (vl-description-has-comments-p x))
        ;; This is something like a vardecl that doesn't have its own warnings,
        ;; so there's nothing to do.
        (mv x warnings))

       (min (vl-description->minloc x))
       (max (vl-description->maxloc x))
       ((mv between beyond)
        (vl-filter-warnings-by-loc min max warnings nil nil))

       ((unless (consp between))
        ;; None of these warnings belong to X, so there is nothing to do.
        (mv x warnings))

       (new-x (vl-description-add-warnings x between)))
    (mv new-x beyond))
  ///
  (more-returns
   (new-x (equal (vl-description->name new-x)
                 (vl-description->name x))
          :name vl-description->name-of-vl-description-inject-warnings)))

(define vl-descriptionlist-inject-warnings
  :short "Extract and attach in-bounds warnings to a description list."
  ((x        vl-descriptionlist-p "Descriptions to attach to.")
   (warnings vl-warninglist-p     "List of early warnings."))
  :returns
  (mv (new-x  vl-descriptionlist-p "Perhaps with warnings added.")
      (beyond vl-warninglist-p     "Warnings that did not get attached."))
  :measure (len x)
  (b* ((x        (vl-descriptionlist-fix x))
       (warnings (vl-warninglist-fix warnings))
       ((when (atom x))
        ;; No descriptions left, so we're done.
        (mv nil warnings))
       ((when (atom warnings))
        ;; Optimization(?): No warnings left to attach, so we may as well be
        ;; done.
        (mv x nil))
       ((mv first warnings)
        (vl-description-inject-warnings (car x) warnings))
       ((mv rest warnings)
        (vl-descriptionlist-inject-warnings (cdr x) warnings)))
    (mv (cons first rest) warnings))
  ///
  (more-returns
   (new-x (equal (vl-descriptionlist->names new-x)
                 (vl-descriptionlist->names x))
          :name vl-descriptionlist->names-of-vl-descriptionlist-inject-warnings)))


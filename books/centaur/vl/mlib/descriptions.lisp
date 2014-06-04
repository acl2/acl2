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
(local (xdoc::set-default-parents vl-description-p))


;; Things that are common to all descriptions:
;;
;;   - Name
;;   - Minloc/Maxloc
;;   - Comments
;;   - Warnings
;;   - Atts
;;
;; We now introduce an abstraction layer for working with these fields, for
;; arbitrary descriptions.

(define vl-description->name ((x vl-description-p))
  :returns (name stringp :rule-classes :type-prescription)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-module->name x))
      (:vl-udp       (vl-udp->name x))
      (:vl-package   (vl-package->name x))
      (:vl-interface (vl-interface->name x))
      (:vl-program   (vl-program->name x))
      (otherwise     (vl-config->name x)))))

(define vl-description->warnings ((x vl-description-p))
  :returns (warnings vl-warninglist-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-module->warnings x))
      (:vl-udp       (vl-udp->warnings x))
      (:vl-package   (vl-package->warnings x))
      (:vl-interface (vl-interface->warnings x))
      (:vl-program   (vl-program->warnings x))
      (otherwise     (vl-config->warnings x)))))

(define vl-description->minloc ((x vl-description-p))
  :returns (minloc vl-location-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-module->minloc x))
      (:vl-udp       (vl-udp->minloc x))
      (:vl-package   (vl-package->minloc x))
      (:vl-interface (vl-interface->minloc x))
      (:vl-program   (vl-program->minloc x))
      (otherwise     (vl-config->minloc x)))))

(define vl-description->maxloc ((x vl-description-p))
  :returns (maxloc vl-location-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-module->maxloc x))
      (:vl-udp       (vl-udp->maxloc x))
      (:vl-package   (vl-package->maxloc x))
      (:vl-interface (vl-interface->maxloc x))
      (:vl-program   (vl-program->maxloc x))
      (otherwise     (vl-config->maxloc x)))))

(define vl-description->comments ((x vl-description-p))
  :returns (comments vl-commentmap-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-module->comments x))
      (:vl-udp       (vl-udp->comments x))
      (:vl-package   (vl-package->comments x))
      (:vl-interface (vl-interface->comments x))
      (:vl-program   (vl-program->comments x))
      (otherwise     (vl-config->comments x)))))

(define vl-description->atts ((x vl-description-p))
  :returns (atts vl-atts-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-module->atts x))
      (:vl-udp       (vl-udp->atts x))
      (:vl-package   (vl-package->atts x))
      (:vl-interface (vl-interface->atts x))
      (:vl-program   (vl-program->atts x))
      (otherwise     (vl-config->atts x)))))

(define change-vl-description-main-fn ((x        vl-description-p)
                                       (name     stringp)
                                       (warnings vl-warninglist-p)
                                       (minloc   vl-location-p)
                                       (maxloc   vl-location-p)
                                       (comments vl-commentmap-p)
                                       (atts     vl-atts-p))
  :returns (new-x vl-description-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module (change-vl-module x
                                    :name name
                                    :warnings warnings
                                    :minloc minloc
                                    :maxloc maxloc
                                    :comments comments
                                    :atts atts))
      (:vl-udp (change-vl-udp x
                              :name name
                              :warnings warnings
                              :minloc minloc
                              :maxloc maxloc
                              :comments comments
                              :atts atts))
      (:vl-package (change-vl-package x
                                      :name name
                                      :warnings warnings
                                      :minloc minloc
                                      :maxloc maxloc
                                      :comments comments
                                      :atts atts))
      (:vl-interface (change-vl-interface x
                                          :name name
                                          :warnings warnings
                                          :minloc minloc
                                          :maxloc maxloc
                                          :comments comments
                                          :atts atts))
      (:vl-program (change-vl-program x
                                      :name name
                                      :warnings warnings
                                      :minloc minloc
                                      :maxloc maxloc
                                      :comments comments
                                      :atts atts))
      (otherwise (change-vl-config x
                                   :name name
                                   :warnings warnings
                                   :minloc minloc
                                   :maxloc maxloc
                                   :comments comments
                                   :atts atts))))
  ///
  (defrule change-vl-description-main-fn-basics
    (b* ((new-x (change-vl-description-main-fn x
                                               name
                                               warnings
                                               minloc
                                               maxloc
                                               comments
                                               atts)))
      (and (equal (vl-description->name new-x)     (string-fix name))
           (equal (vl-description->warnings new-x) (vl-warninglist-fix warnings))
           (equal (vl-description->minloc new-x)   (vl-location-fix minloc))
           (equal (vl-description->maxloc new-x)   (vl-location-fix maxloc))
           (equal (vl-description->comments new-x) (vl-commentmap-fix comments))
           (equal (vl-description->atts new-x)     (vl-atts-fix atts))))
    :enable (vl-description->name
             vl-description->warnings
             vl-description->minloc
             vl-description->maxloc
             vl-description->comments
             vl-description->atts)))

(defmacro change-vl-description (var &rest args)
  (b* ((alist
        ;; Binds any present keywords to their values
        (std::da-changer-args-to-alist args
                                  '(:name :warnings :minloc
                                          :maxloc :comments :atts)))
       ((fun (g key accessor alist))
        (if (assoc key alist)
            (check-vars-not-free (change-vl-description-var)
                                 (cdr (assoc key alist)))
          `(,accessor change-vl-description-var))))
    `(let ((change-vl-description-var ,var))
       (change-vl-description-main-fn
        change-vl-description-var
        ,(g :name 'vl-description->name alist)
        ,(g :warnings 'vl-description->warnings alist)
        ,(g :minloc 'vl-description->minloc alist)
        ,(g :maxloc 'vl-description->maxloc alist)
        ,(g :comments 'vl-description->comments alist)
        ,(g :atts 'vl-description->atts alist)))))

(defprojection vl-descriptionlist->names ((x vl-descriptionlist-p))
  :returns (names string-listp)
  (vl-description->name x))



(fty::defalist vl-descalist
  :key-type stringp
  :val-type vl-description-p)

(defalist vl-descalist-p (x)
  :key (stringp x)
  :val (vl-description-p x)
  :keyp-of-nil nil
  :valp-of-nil nil
  :already-definedp t)

(define vl-descalist ((x vl-descriptionlist-p))
  :returns (alist vl-descalist-p)
  (if (atom x)
      nil
    (hons-acons (vl-description->name (car x))
                (vl-description-fix (car x))
                (vl-descalist (cdr x)))))



(define vl-find-description
  :short "@(call vl-find-description) retrieves the first description named
@('x') from @('descs')."
  ((name stringp)
   (descs vl-descriptionlist-p))
  :hooks ((:fix :args ((descs vl-descriptionlist-p))))
  :long "<p>This is the logically simplest expression of looking up a description,
and is our preferred normal form for rewriting.</p>

<p>This function is not efficient.  It carries out an @('O(n)') search of the
descriptions.  See @(see vl-fast-find-description) for a faster alternative.</p>"
  (cond ((atom descs)
         nil)
        ((equal name (vl-description->name (car descs)))
         (vl-description-fix (car descs)))
        (t
         (vl-find-description name (cdr descs))))
  ///
  (defthm vl-find-description-when-not-consp
    (implies (not (consp descs))
             (equal (vl-find-description name descs)
                    nil)))

  (defthm vl-find-description-of-cons
    (equal (vl-find-description name (cons a x))
           (if (equal name (vl-description->name a))
               (vl-description-fix a)
             (vl-find-description name x))))

  (defthm vl-description-p-of-vl-find-description
    (equal (vl-description-p (vl-find-description name descs))
           (if (member-equal name (vl-descriptionlist->names descs))
               t
             nil)))

  (defthm vl-find-description-under-iff
    (iff (vl-find-description name descs)
         (member-equal name (vl-descriptionlist->names descs))))

  (defthm vl-description->name-of-vl-find-description
    (implies (vl-find-description name descs)
             (equal (vl-description->name (vl-find-description name descs))
                    (string-fix name))))

  (deffixequiv vl-find-description :args ((descs vl-descriptionlist-p))))


(define vl-fast-find-description ((name         stringp)
                                  (descriptions vl-descriptionlist-p)
                                  (descalist    (equal descalist (vl-descalist descriptions))))
  :enabled t
  :inline t
  :hooks nil
  (mbe :logic (vl-find-description name descriptions)
       :exec (cdr (hons-get name descalist)))
  :prepwork
  ((local (defthm l0
            (implies (and (vl-descriptionlist-p descriptions)
                          (stringp name))
                     (equal (cdr (hons-assoc-equal name (vl-descalist descriptions)))
                            (vl-find-description name descriptions)))
            :hints(("Goal" :in-theory (enable vl-descalist)))))))

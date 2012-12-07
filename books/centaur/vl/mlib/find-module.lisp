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

; find-module.lisp -- basic functions for looking up modules.
;
; Note: this just includes very basic tools.  See also hierarchy.lisp, which
; includes several others.

(defsection vl-has-module
  :parents (hierarchy)
  :short "@(call vl-has-module) determines if a module named @('name') is
defined in @('mods')."

  :long "<p>We leave this function enabled.  In the logic, it is defined as
nothing more than membership in @('(@(see vl-modulelist->names) mods)').</p>

<p>This function is not efficient.  It carries out an @('O(n)') search of the
modules.  See @(see vl-fast-has-module) for a faster alternative.</p>"

  (defun vl-has-module (name mods)
    (declare (xargs :guard (and (stringp name)
                                (vl-modulelist-p mods))))
    (mbe :logic
         (if (member-equal name (vl-modulelist->names mods))
             t
           nil)
         :exec
         (if (atom mods)
             nil
           (or (equal name (vl-module->name (car mods)))
               (vl-has-module name (cdr mods)))))))


(defsection vl-find-module
  :parents (hierarchy)
  :short "@(call vl-find-module) retrieves the first module named @('x') from
@('mods')."

  :long "<p>This is the logically simplest expression of looking up a module,
and is our preferred normal form for rewriting.</p>

<p>This function is not efficient.  It carries out an @('O(n)') search of the
modules.  See @(see vl-fast-find-module) for a faster alternative.</p>"

  (defund vl-find-module (name mods)
    (declare (xargs :guard (and (stringp name)
                                (vl-modulelist-p mods))))
    (cond ((atom mods)
           nil)
          ((equal name (vl-module->name (car mods)))
           (car mods))
          (t
           (vl-find-module name (cdr mods)))))

  (local (in-theory (enable vl-find-module)))

  (defthm vl-find-module-when-not-consp
    (implies (not (consp mods))
             (equal (vl-find-module name mods)
                    nil)))

  (defthm vl-find-module-of-cons
    (equal (vl-find-module name (cons a x))
           (if (equal name (vl-module->name a))
               a
             (vl-find-module name x))))

  (defthm vl-module-p-of-vl-find-module
    (implies (force (vl-modulelist-p mods))
             (equal (vl-module-p (vl-find-module name mods))
                    (vl-has-module name mods))))

  (defthm vl-find-module-under-iff
    (implies (force (vl-modulelist-p mods))
             (iff (vl-find-module name mods)
                  (vl-has-module name mods))))

  (defthm vl-module->name-of-vl-find-module
    (equal (vl-module->name (vl-find-module name mods))
           (if (vl-has-module name mods)
               name
             nil))
    :hints(("Goal" :in-theory (enable vl-module->name))))

  (defthm member-equal-of-vl-find-module-of-self
    (implies (force (vl-modulelist-p mods))
             (iff (member-equal (vl-find-module name mods) mods)
                  (vl-has-module name mods)))))


(defalist vl-modalist-p (x)
  :key (stringp x)
  :val (vl-module-p x)
  :keyp-of-nil nil
  :valp-of-nil nil
  :parents (hierarchy)
  :short "An alist mapping module names to modules."
  :long "<p>A modalist is generally constructed by @(see vl-modalist).</p>")


(defsection vl-modalist
  :parents (hierarchy)
  :short "Build a fast alist mapping module names to modules."

  :long "<p>@(call vl-modalist) constructs a fast alist that binds each
module's name to its definition.  This alist can be given to functions like
@(see vl-fast-has-module), @(see vl-fast-find-module), etc., to implement fast
module lookups.</p>"

  (defund vl-modalist (mods)
    (declare (xargs :guard (vl-modulelist-p mods)))
    (if (atom mods)
        nil
      (hons-acons (vl-module->name (car mods))
                  (car mods)
                  (vl-modalist (cdr mods)))))

  (local (in-theory (enable vl-modalist)))

  (defthm vl-modalist-when-not-consp
    (implies (not (consp x))
             (equal (vl-modalist x)
                    nil)))

  (defthm vl-modalist-of-cons
    (equal (vl-modalist (cons a x))
           (cons (cons (vl-module->name a) a)
                 (vl-modalist x))))

  (defthm alistp-of-vl-modalist
    (alistp (vl-modalist x)))

  (defthm strip-cars-of-vl-modalist
    (equal (strip-cars (vl-modalist x))
           (vl-modulelist->names x)))

  (defthm strip-cdrs-of-vl-modalist
    (equal (strip-cdrs (vl-modalist x))
           (list-fix x)))

  (defthm hons-assoc-equal-of-vl-modalist
    (equal (hons-assoc-equal name (vl-modalist x))
           (if (vl-has-module name x)
               (cons name (vl-find-module name x))
             nil))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-modalist-p-of-vl-modalist
    (implies (force (vl-modulelist-p x))
             (vl-modalist-p (vl-modalist x)))))


(defsection vl-fast-has-module
  :parents (hierarchy)
  :short "@(see vl-modalist)-optimized version of @(see vl-has-module)."

  (definline vl-fast-has-module (name mods modalist)
    (declare (xargs :guard (and (stringp name)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))))
             (ignorable mods))
    (mbe :logic
         (vl-has-module name mods)
         :exec
         (if (hons-get name modalist)
             t
           nil))))


(defsection vl-fast-find-module
  :parents (hierarchy)
  :short "@(see vl-modalist)-optimized version of @(see vl-find-module)."

  (definline vl-fast-find-module (name mods modalist)
    (declare (xargs :guard (and (stringp name)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))))
             (ignorable mods))
    (mbe :logic
         (vl-find-module name mods)
         :exec
         (cdr (hons-get name modalist)))))


(defsection vl-has-modules
  :parents (hierarchy)
  :short "@(call vl-has-modules) determines if every module in named in @('x')
is defined in @('mods')."

  :long "<p>We leave this function enabled.  In the logic, it is defined as
nothing more a subsetp-equal check in @('(@(see vl-modulelist->names)
mods)').</p>

<p>This function is not efficient.  It carries out a linear search through the
list of modules for each name in @('x'), making it quadratic.  See also @(see
vl-fast-has-modules) for a faster alternative.</p>"

  (defun vl-has-modules (x mods)
    (declare (xargs :guard (and (string-listp x)
                                (vl-modulelist-p mods))))
    (mbe :logic
         (subsetp-equal x (vl-modulelist->names mods))
         :exec
         (or (atom x)
             (and (vl-has-module (car x) mods)
                  (vl-has-modules (cdr x) mods))))))


(defsection vl-fast-has-modules
  :parents (hierarchy)
  :short "@(see vl-modalist)-optimized version of @(see vl-has-modules)."

  (defun vl-fast-has-modules (x mods modalist)
    (declare (xargs :guard (and (string-listp x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (mbe :logic
         (subsetp-equal x (vl-modulelist->names mods))
         :exec
         (or (atom x)
             (and (vl-fast-has-module (car x) mods modalist)
                  (vl-fast-has-modules (cdr x) mods modalist))))))


(defprojection vl-find-modules (x mods)
  (vl-find-module x mods)
  :guard (and (string-listp x)
              (vl-modulelist-p mods))
  :parents (hierarchy)
  :short "@(call vl-find-modules) gathers every module in named in @('x') from
@('mods') and returns them as a list."

  :long "<p>This is a simple projection over @(see vl-find-module), and is our
logically simplest way of gathering modules by name.</p>

<p>This function is not efficient.  It carries out a linear search over the
module list for each module in @('x'), making it quadratic.  For better
performance, see @(see vl-fast-find-modules).</p>"

  :rest
  ((defthm vl-modulelist-p-of-vl-find-modules
     (implies (force (vl-modulelist-p mods))
              (equal (vl-modulelist-p (vl-find-modules names mods))
                     (vl-has-modules names mods))))

   (defthm subsetp-equal-of-vl-find-modules-of-self
     (implies (force (vl-modulelist-p mods))
              (equal (subsetp-equal (vl-find-modules names mods) mods)
                     (vl-has-modules names mods))))

   (defthm vl-modulelist-p-of-vl-find-modules-of-self
     (implies (force (vl-modulelist-p mods))
              (equal (vl-modulelist-p (vl-find-modules names mods))
                     (vl-has-modules names mods))))

   (defthm vl-modulelist->names-of-vl-find-modules
     (implies (vl-has-modules names mods)
              (equal (vl-modulelist->names (vl-find-modules names mods))
                     (list-fix names))))))


(defsection vl-fast-find-modules
  :parents (hierarchy)
  :short "@(see vl-modalist)-optimized version of @(see vl-find-modules)."

  (defun vl-fast-find-modules (x mods modalist)
    (declare (xargs :guard (and (string-listp x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (mbe :logic
         (vl-find-modules x mods)
         :exec
         (if (atom x)
             nil
           (cons (vl-fast-find-module (car x) mods modalist)
                 (vl-fast-find-modules (cdr x) mods modalist))))))

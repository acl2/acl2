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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (xdoc::set-default-parents hierarchy))

; find-module.lisp -- basic functions for looking up modules.
;
; Note: this just includes very basic tools.  See also hierarchy.lisp, which
; includes several others.

(define vl-has-module
  :short "@(call vl-has-module) determines if a module named @('name') is
defined in @('mods')."
  ((name stringp)
   (mods vl-modulelist-p))
  :long "<p>We leave this function enabled.  In the logic, it is defined as
nothing more than membership in @('(vl-modulelist->names mods)').</p>

<p>This function is not efficient.  It carries out an @('O(n)') search of the
modules.  See @(see vl-fast-has-module) for a faster alternative.</p>"
  :enabled t
  (mbe :logic
       (if (member-equal name (vl-modulelist->names mods))
           t
         nil)
       :exec
       (if (atom mods)
           nil
         (or (equal name (vl-module->name (car mods)))
             (vl-has-module name (cdr mods)))))
  ///
  (deffixequiv vl-has-module :args ((mods vl-modulelist-p))))


(define vl-find-module
  :short "@(call vl-find-module) retrieves the first module named @('x') from
@('mods')."
  ((name stringp)
   (mods vl-modulelist-p))
  :long "<p>This is the logically simplest expression of looking up a module,
and is our preferred normal form for rewriting.</p>

<p>This function is not efficient.  It carries out an @('O(n)') search of the
modules.  See @(see vl-fast-find-module) for a faster alternative.</p>"
  (cond ((atom mods)
         nil)
        ((equal name (vl-module->name (car mods)))
         (vl-module-fix (car mods)))
        (t
         (vl-find-module name (cdr mods))))
  ///
  (defthm vl-find-module-when-not-consp
    (implies (not (consp mods))
             (equal (vl-find-module name mods)
                    nil)))

  (defthm vl-find-module-of-cons
    (equal (vl-find-module name (cons a x))
           (if (equal name (vl-module->name a))
               (vl-module-fix a)
             (vl-find-module name x))))

  (defthm vl-module-p-of-vl-find-module
    (equal (vl-module-p (vl-find-module name mods))
           (vl-has-module name mods)))

  (defthm vl-find-module-under-iff
    (iff (vl-find-module name mods)
         (vl-has-module name mods)))

  (defthm vl-module->name-of-vl-find-module
    (implies (vl-has-module name mods)
             (equal (vl-module->name (vl-find-module name mods))
                    (string-fix name))))

  (defthm member-equal-of-vl-find-module-of-self
    (implies (force (vl-modulelist-p mods))
             (iff (member-equal (vl-find-module name mods) mods)
                  (vl-has-module name mods))))

  (deffixequiv vl-find-module :args ((mods vl-modulelist-p))))


(fty::defalist vl-modalist
  :key-type stringp
  :val-type vl-module-p)

(defalist vl-modalist-p (x)
  :key (stringp x)
  :val (vl-module-p x)
  :keyp-of-nil nil
  :valp-of-nil nil
  :already-definedp t
  :short "An alist mapping module names to modules."
  :long "<p>A modalist is generally constructed by @(see vl-modalist).</p>")


(define vl-modalist
  :short "Build a fast alist mapping module names to modules."
  ((mods vl-modulelist-p))
  :returns (modalist vl-modalist-p)
  :long "<p>@(call vl-modalist) constructs a fast alist that binds each
module's name to its definition.  This alist can be given to functions like
@(see vl-fast-has-module), @(see vl-fast-find-module), etc., to implement fast
module lookups.</p>"

  (if (atom mods)
      nil
    (hons-acons (vl-module->name (car mods))
                (vl-module-fix (car mods))
                (vl-modalist (cdr mods))))
  ///
  (defthm vl-modalist-when-not-consp
    (implies (not (consp x))
             (equal (vl-modalist x)
                    nil)))

  (defthm vl-modalist-of-cons
    (equal (vl-modalist (cons a x))
           (cons (cons (vl-module->name a)
                       (vl-module-fix a))
                 (vl-modalist x))))

  (defthm alistp-of-vl-modalist
    (alistp (vl-modalist x)))

  (defthm strip-cars-of-vl-modalist
    (equal (strip-cars (vl-modalist x))
           (vl-modulelist->names x)))

  (defthm strip-cdrs-of-vl-modalist
    (equal (strip-cdrs (vl-modalist x))
           (vl-modulelist-fix (list-fix x))))

  (defthm hons-assoc-equal-of-vl-modalist
    (equal (hons-assoc-equal name (vl-modalist x))
           (if (vl-has-module name x)
               (cons name (vl-find-module name x))
             nil)))

  (deffixequiv vl-modalist))


(define vl-fast-has-module
  :short "@(see vl-modalist)-optimized version of @(see vl-has-module)."
  ((name     stringp)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :inline t
  :enabled t
  (mbe :logic (vl-has-module name mods)
       :exec (if (hons-get name modalist)
                 t
               nil)))

(define vl-fast-find-module
  :short "@(see vl-modalist)-optimized version of @(see vl-find-module)."
  ((name     stringp)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :inline t
  :enabled t
  (mbe :logic (vl-find-module name mods)
       :exec (cdr (hons-get name modalist))))

(define vl-has-modules
  :short "@(call vl-has-modules) determines if every module in named in @('x')
is defined in @('mods')."

  ((x    string-listp)
   (mods vl-modulelist-p))

  :long "<p>We leave this function enabled.  In the logic, it is defined as
nothing more a subsetp-equal check in @('(vl-modulelist->names mods)').</p>

<p>This function is not efficient.  It carries out a linear search through the
list of modules for each name in @('x'), making it quadratic.  See also @(see
vl-fast-has-modules) for a faster alternative.</p>"

  :enabled t
  (mbe :logic
       (subsetp-equal x (vl-modulelist->names mods))
       :exec
       (or (atom x)
           (and (vl-has-module (car x) mods)
                (vl-has-modules (cdr x) mods))))
  ///
  (deffixequiv vl-has-modules :args ((mods vl-modulelist-p))))

(define vl-fast-has-modules
  :short "@(see vl-modalist)-optimized version of @(see vl-has-modules)."
  ((x        string-listp)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :enabled t
  (mbe :logic (subsetp-equal (string-list-fix x) (vl-modulelist->names mods))
       :exec (or (atom x)
                 (and (vl-fast-has-module (car x) mods modalist)
                      (vl-fast-has-modules (cdr x) mods modalist)))))


(defprojection vl-find-modules ((x    string-listp)
                                (mods vl-modulelist-p))
  (vl-find-module x mods)
  :short "@(call vl-find-modules) gathers every module in named in @('x') from
@('mods') and returns them as a list."

  :long "<p>This is a simple projection over @(see vl-find-module), and is our
logically simplest way of gathering modules by name.</p>

<p>This function is not efficient.  It carries out a linear search over the
module list for each module in @('x'), making it quadratic.  For better
performance, see @(see vl-fast-find-modules).</p>"
  ///
  (defthm vl-modulelist-p-of-vl-find-modules
    (equal (vl-modulelist-p (vl-find-modules names mods))
           (vl-has-modules names mods)))

  (defthm subsetp-equal-of-vl-find-modules-of-self
    (implies (vl-modulelist-p mods)
             (equal (subsetp-equal (vl-find-modules names mods) mods)
                    (vl-has-modules names mods))))

  (defthm vl-modulelist->names-of-vl-find-modules
    (implies (vl-has-modules names mods)
             (equal (vl-modulelist->names (vl-find-modules names mods))
                    (string-list-fix names)))))

(define vl-fast-find-modules
  :short "@(see vl-modalist)-optimized version of @(see vl-find-modules)."
  ((x        string-listp)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :enabled t
  (mbe :logic (vl-find-modules x mods)
       :exec (if (atom x)
                 nil
               (cons (vl-fast-find-module (car x) mods modalist)
                     (vl-fast-find-modules (cdr x) mods modalist)))))

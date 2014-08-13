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
(include-book "../mlib/modnamespace")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))

(defxdoc unparam-check
  :short "Sanity check for ensuring that parameters aren't shadowed by local
declarations within functions, tasks, or other statements."

  :long "<p>To keep @(see unparameterization) simple, we don't try to support
modules where parameter names are shadowed by local names within functions,
tasks, and other named statements within, e.g., always or initial blocks.</p>

<p>This is a simple transformation that looks for modules that have any such
name clashes, and adds fatal warnings to them.</p>")

(local (xdoc::set-default-parents unparam-check))

(define vl-blockitem->name ((x vl-blockitem-p))
  :returns (name stringp)
  (let ((x (vl-blockitem-fix x)))
    (case (tag x)
      (:vl-vardecl   (vl-vardecl->name x))
      (otherwise     (vl-paramdecl->name x)))))

(defprojection vl-blockitemlist->names ((x vl-blockitemlist-p))
  :returns (names string-listp)
  (vl-blockitem->name x))

(defines vl-stmt-localnames-nrev
  :flag-local nil

  (define vl-stmt-localnames-nrev ((x vl-stmt-p) nrev)
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* (((when (vl-atomicstmt-p x))
          (nrev-fix nrev))
         (nrev (vl-blockitemlist->names-nrev (vl-compoundstmt->decls x) nrev))
         (nrev (vl-stmtlist-localnames-nrev (vl-compoundstmt->stmts x) nrev)))
      nrev))

  (define vl-stmtlist-localnames-nrev ((x vl-stmtlist-p) nrev)
    :measure (vl-stmtlist-count x)
    :flag :list
    (b* (((when (atom x))
          (nrev-fix nrev))
         (nrev (vl-stmt-localnames-nrev (car x) nrev))
         (nrev (vl-stmtlist-localnames-nrev (cdr x) nrev)))
      nrev)))

(defines vl-stmt-localnames

  (define vl-stmt-localnames
    ((x vl-stmt-p))
    :returns (names string-listp)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (mbe :logic
         (if (vl-atomicstmt-p x)
             nil
           (append (vl-blockitemlist->names (vl-compoundstmt->decls x))
                   (vl-stmtlist-localnames (vl-compoundstmt->stmts x))))
         :exec
         (with-local-nrev (vl-stmt-localnames-nrev x nrev))))

  (define vl-stmtlist-localnames
    ((x vl-stmtlist-p))
    :returns (names string-listp)
    :measure (vl-stmtlist-count x)
    (mbe :logic (if (atom x)
                    nil
                  (append (vl-stmt-localnames (car x))
                          (vl-stmtlist-localnames (cdr x))))
         :exec
         (with-local-nrev (vl-stmtlist-localnames-nrev x nrev))))
  ///
  (defthm-vl-stmt-localnames-nrev-flag
    (defthm vl-stmt-localnames-nrev-removal
      (equal (vl-stmt-localnames-nrev x nrev)
             (append nrev (vl-stmt-localnames x)))
      :flag :stmt)
    (defthm vl-stmtlist-localnames-nrev-removal
      (equal (vl-stmtlist-localnames-nrev x nrev)
             (append nrev (vl-stmtlist-localnames x)))
      :flag :list)
    :hints(("Goal"
            :expand ((vl-stmt-localnames x)
                     (vl-stmtlist-localnames x)
                     (vl-stmt-localnames-nrev x nrev)
                     (vl-stmtlist-localnames-nrev x nrev)))))

  (verify-guards vl-stmtlist-localnames)
  (deffixequiv-mutual vl-stmt-localnames))

(define vl-fundecl-localnames-nrev ((x vl-fundecl-p) nrev)
  (b* (((vl-fundecl x) x)
       (nrev (vl-taskportlist->names-nrev x.inputs nrev))
       (nrev (vl-blockitemlist->names-nrev x.decls nrev))
       (nrev (vl-stmt-localnames-nrev x.body nrev)))
    nrev))

(define vl-fundecl-localnames ((x vl-fundecl-p))
  :returns (names string-listp)
  :verify-guards nil
  (mbe :logic
       (b* (((vl-fundecl x) x))
         (append (vl-taskportlist->names x.inputs)
                 (vl-blockitemlist->names x.decls)
                 (vl-stmt-localnames x.body)))
       :exec
       (with-local-nrev
         (vl-fundecl-localnames-nrev x nrev)))
  ///
  (defthm vl-fundecl-localnames-nrev-removal
    (equal (vl-fundecl-localnames-nrev x nrev)
           (append nrev (vl-fundecl-localnames x)))
    :hints(("Goal" :in-theory (enable vl-fundecl-localnames-nrev))))

  (verify-guards vl-fundecl-localnames))

(defmapappend vl-fundecllist-localnames (x)
  (vl-fundecl-localnames x)
  :guard (vl-fundecllist-p x)
  :rest
  ((defthm string-listp-of-vl-fundecllist-localnames
     (string-listp (vl-fundecllist-localnames x)))))

(define vl-taskdecl-localnames-nrev ((x vl-taskdecl-p) nrev)
  (b* (((vl-taskdecl x) x)
       (nrev (vl-taskportlist->names-nrev x.ports nrev))
       (nrev (vl-blockitemlist->names-nrev x.decls nrev))
       (nrev (vl-stmt-localnames-nrev x.body nrev)))
    nrev))

(define vl-taskdecl-localnames ((x vl-taskdecl-p))
  :returns (names string-listp)
  :verify-guards nil
  (mbe :logic
       (b* (((vl-taskdecl x) x))
         (append (vl-taskportlist->names x.ports)
                 (vl-blockitemlist->names x.decls)
                 (vl-stmt-localnames x.body)))
       :exec
       (with-local-nrev
         (vl-taskdecl-localnames-nrev x nrev)))
  ///
  (defthm vl-taskdecl-localnames-nrev-removal
    (equal (vl-taskdecl-localnames-nrev x nrev)
           (append nrev (vl-taskdecl-localnames x)))
    :hints(("Goal" :in-theory (enable vl-taskdecl-localnames-nrev))))

  (verify-guards vl-taskdecl-localnames))

(defmapappend vl-taskdecllist-localnames (x)
  (vl-taskdecl-localnames x)
  :guard (vl-taskdecllist-p x)
  :rest
  ((defthm string-listp-of-vl-taskdecllist-localnames
     (string-listp (vl-taskdecllist-localnames x)))))

(define vl-always-localnames-nrev ((x vl-always-p) nrev)
  (b* (((vl-always x) x))
    (vl-stmt-localnames-nrev x.stmt nrev)))

(define vl-always-localnames ((x vl-always-p))
  :returns (names string-listp)
  :verify-guards nil
  (mbe :logic
       (b* (((vl-always x) x))
         (vl-stmt-localnames x.stmt))
       :exec
       (with-local-nrev
         (vl-always-localnames-nrev x nrev)))
  ///
  (defthm vl-always-localnames-nrev-removal
    (equal (vl-always-localnames-nrev x nrev)
           (append nrev (vl-always-localnames x)))
    :hints(("Goal" :in-theory (enable vl-always-localnames-nrev))))

  (verify-guards vl-always-localnames))

(defmapappend vl-alwayslist-localnames (x)
  (vl-always-localnames x)
  :guard (vl-alwayslist-p x)
  :rest
  ((defthm string-listp-of-vl-alwayslist-localnames
     (string-listp (vl-alwayslist-localnames x)))))


(define vl-initial-localnames-nrev ((x vl-initial-p) nrev)
  (b* (((vl-initial x) x))
    (vl-stmt-localnames-nrev x.stmt nrev)))

(define vl-initial-localnames ((x vl-initial-p))
  :returns (names string-listp)
  :verify-guards nil
  (mbe :logic
       (b* (((vl-initial x) x))
         (vl-stmt-localnames x.stmt))
       :exec
       (with-local-nrev
         (vl-initial-localnames-nrev x nrev)))
  ///
  (defthm vl-initial-localnames-nrev-removal
    (equal (vl-initial-localnames-nrev x nrev)
           (append nrev (vl-initial-localnames x)))
    :hints(("Goal" :in-theory (enable vl-initial-localnames-nrev))))

  (verify-guards vl-initial-localnames))

(defmapappend vl-initiallist-localnames (x)
  (vl-initial-localnames x)
  :guard (vl-initiallist-p x)
  :rest
  ((defthm string-listp-of-vl-initiallist-localnames
     (string-listp (vl-initiallist-localnames x)))))

(define vl-module-localnames
  :short "Collect up names that are used as local names within functions,
          tasks, and other statements."
  ((x vl-module-p))
  :returns (localnames string-listp)
  (b* (((vl-module x) x))
    (append (vl-taskdecllist-localnames x.taskdecls)
            (vl-fundecllist-localnames x.fundecls)
            (vl-alwayslist-localnames x.alwayses)
            (vl-initiallist-localnames x.initials))))

(define vl-module-unparam-check ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        x)
       ((unless (consp x.paramdecls))
        ;; Optimization: nothing to check, no need to gather local names.
        x)

       (localnames (mergesort (vl-module-localnames x)))
       (paramnames (mergesort (vl-paramdecllist->names x.paramdecls)))
       (overlap    (intersect localnames paramnames))

       ((unless overlap)
        ;; Fine, no overlap, no worries.
        x)

       (warnings (fatal :type :vl-unparam-fail
                        :msg "Cowardly refusing to attempt unparameterization ~
                              because some parameter names are shadowed ~
                              within functions, tasks, or other local blocks, ~
                              and this just seems error-prone: ~&0."
                        :args (list overlap)
                        :acc x.warnings)))
    (change-vl-module x :warnings warnings)))

(defprojection vl-modulelist-unparam-check ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-unparam-check x))

(define vl-design-unparam-check ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-unparam-check x.mods))))


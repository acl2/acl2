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



(defxdoc filtering-by-name
  :parents (mlib)
  :short "Functions for filtering lists of module elements by their names."

  :long "<p>We implement functions for keeping and deleting elements by their
names, and also for partitioning lists into named and unnamed subsets.</p>

<p>Our implementations are logically simple, but we use MBE to make them fairly
efficient.  In particular, suppose we want to keep, delete, or filter the list
<tt>X</tt> using some list of <tt>NAMES</tt>.  If there are only a few names,
we use naive algorithm that calls <tt>member-equal</tt> repeatedly, and this is
effectively <tt>O(|X|)</tt>.</p>

<p>When there are many names, we use @(see make-lookup-alist) to construct a
temporary, fast alist, and use @(see fast-memberp) to perform the lookups.
Assuming that hashing operations are constant time, constructing this table is
<tt>O(|NAMES|)</tt>, and the subsequent processing of <tt>X</tt> is
<tt>O(|X|)</tt>.</p>")

(defund def-vl-filter-by-name-fn
  (type          ;; should be 'netdecl, 'regdecl, 'vardecl, 'module, etc.
   keep-long     ;; extra documentation for the keep function
   del-long      ;; extra documentation for the delete function
   filter-long   ;; extra documentation for the filter function
   short-name    ;; e.g., "name", "modname", "instname"
   accessor      ;; e.g., vl-netdecl->name
   suffix        ;; e.g., "netdecls" or "events" or "modinsts-by-name"
   )
  (declare (xargs :guard (and (symbolp type)
                              (stringp keep-long)
                              (stringp del-long)
                              (stringp filter-long)
                              (stringp short-name)
                              (symbolp suffix)
                              (symbolp accessor)
                              )))
  (let* ((mksym-package-symbol 'vl::foo)
         (type->name   accessor)
         (list-p       (mksym 'vl- type 'list-p))
         (fast-fn      (mksym 'vl-fast-filter- suffix))
         (fn           (mksym 'vl-filter- suffix))
         (del-fn       (mksym 'vl-delete- suffix))
         (slow-del-fn  (mksym 'vl-slow-delete- suffix))
         (fast-del-fn  (mksym 'vl-fast-delete- suffix))
         (keep-fn      (mksym 'vl-keep- suffix))
         (slow-keep-fn (mksym 'vl-slow-keep- suffix))
         (fast-keep-fn (mksym 'vl-fast-keep- suffix))
         )
    `(defsection ,fn

       (defxdoc ,keep-fn
         :parents (filtering-by-name)
         :short ,(cat "Keep @(see vl-" (symbol-name type) "-p)s by "
short-name ".")

         :long ,(cat "<p>We are given <tt>names</tt>, a list of strings, and
<tt>x</tt>, a list of @(see vl-" (symbol-name type) "-p)s.  We return all of the
members of <tt>x</tt> whose " short-name "s are in <tt>names</tt>.</p>"

keep-long

"<h3>Definition</h3>

<p>Note that we actually use <tt>nreverse</tt> under the hood.</p>

@(def " (symbol-name keep-fn) ")
@(def " (symbol-name slow-keep-fn) ")
@(def " (symbol-name fast-keep-fn) ")"))


       (defxdoc ,del-fn
         :parents (filtering-by-name)
         :short ,(cat "Remove @(see vl-" (symbol-name type) "-p)s by "
short-name ".")

         :long ,(cat "<p>We are given <tt>names</tt>, a list of strings, and
<tt>x</tt>, a list of @(see vl-" (symbol-name type) "-p)s.  We remove all of the
members of <tt>x</tt> whose " short-name "s are in <tt>names</tt>.</p>"

del-long

"<h3>Definition</h3>

<p>Note that we actually use <tt>nreverse</tt> under the hood.</p>

@(def " (symbol-name del-fn) ")
@(def " (symbol-name slow-del-fn) ")
@(def " (symbol-name fast-del-fn) ")"))

       (defxdoc ,fn
         :parents (filtering-by-name)
         :short ,(cat "Partition a list of @(see vl-" (symbol-name
type) "-p)s by " short-name ".")

         :long ,(cat "<p><b>Signature</b>: @(call " (symbol-name fn) ")
returns <tt>(mv named unnamed)</tt>.</p>

<p>The only reason to use this function is efficiency.  Logically,
<tt>named</tt> is equal to @(see " (symbol-name keep-fn) ") and
<tt>unnamed</tt> is equal to @(see " (symbol-name del-fn) ").  We leave
this function enabled and would think it odd to ever prove a theorem
about it.</p>"

filter-long

"<h3>Definition</h3>

<p>Note that we actually use <tt>nreverse</tt> under the hood.</p>

@(def " (symbol-name fn) ")
@(def " (symbol-name fast-fn) ")"))

       (defund ,fast-keep-fn (names fal x acc)
         (declare (xargs :guard (and (string-listp names)
                                     (equal fal (make-lookup-alist names))
                                     (,list-p x))))
         (cond ((atom x)
                acc)
               ((fast-memberp (,type->name (car x)) names fal)
                (,fast-keep-fn names fal (cdr x) (cons (car x) acc)))
               (t
                (,fast-keep-fn names fal (cdr x) acc))))

       (defund ,slow-keep-fn (names x)
         (declare (xargs :guard (and (string-listp names)
                                     (,list-p x))))
         (cond ((atom x)
                nil)
               ((member-equal (,type->name (car x)) names)
                (cons (car x) (,slow-keep-fn names (cdr x))))
               (t
                (,slow-keep-fn names (cdr x)))))

       (defund ,keep-fn (names x)
         (declare (xargs :guard (and (string-listp names)
                                     (,list-p x))
                         :verify-guards nil))
         (mbe :logic
              (cond ((atom x)
                     nil)
                    ((member-equal (,type->name (car x)) names)
                     (cons (car x) (,keep-fn names (cdr x))))
                    (t
                     (,keep-fn names (cdr x))))
              :exec
              (b* ((len (length names))
                   ((when (< len 10)) (,slow-keep-fn names x))
                   (fal (make-lookup-alist names))
                   (ans (,fast-keep-fn names fal x nil))
                   (- (fast-alist-free fal)))
                  (reverse ans))))

       (defttag vl-optimize)
       (progn!
        (set-raw-mode t)
        (setf (gethash ',fast-keep-fn ACL2::*never-profile-ht*) t)
        (defun ,keep-fn (names x)
          (b* ((len (length names))
               ((when (< len 10)) (,slow-keep-fn names x))
               (fal (make-lookup-alist names))
               (ans (,fast-keep-fn names fal x nil))
               (- (fast-alist-free fal)))
              (nreverse ans))))
       (defttag nil)



       (defund ,fast-del-fn (names fal x acc)
         (declare (xargs :guard (and (string-listp names)
                                     (equal fal (make-lookup-alist names))
                                     (,list-p x))))
         (cond ((atom x)
                acc)
               ((fast-memberp (,type->name (car x)) names fal)
                (,fast-del-fn names fal (cdr x) acc))
               (t
                (,fast-del-fn names fal (cdr x) (cons (car x) acc)))))

       (defund ,slow-del-fn (names x)
         (declare (xargs :guard (and (string-listp names)
                                     (,list-p x))))
         (cond ((atom x)
                nil)
               ((member-equal (,type->name (car x)) names)
                (,slow-del-fn names (cdr x)))
               (t
                (cons (car x) (,slow-del-fn names (cdr x))))))

       (defund ,del-fn (names x)
         (declare (xargs :guard (and (string-listp names)
                                     (,list-p x))
                         :verify-guards nil))
         (mbe :logic
              (cond ((atom x)
                     nil)
                    ((member-equal (,type->name (car x)) names)
                     (,del-fn names (cdr x)))
                    (t
                     (cons (car x) (,del-fn names (cdr x)))))
              :exec
              (b* ((len (length names))
                   ((when (< len 10)) (,slow-del-fn names x))
                   (fal (make-lookup-alist names))
                   (ans (,fast-del-fn names fal x nil))
                   (- (fast-alist-free fal)))
                  (reverse ans))))

       (defttag vl-optimize)
       (progn!
        (set-raw-mode t)
        (setf (gethash ',fast-del-fn ACL2::*never-profile-ht*) t)
        (defun ,del-fn (names x)
          (b* ((len (length names))
               ((when (< len 10)) (,slow-del-fn names x))
               (fal (make-lookup-alist names))
               (ans (,fast-del-fn names fal x nil))
               (- (fast-alist-free fal)))
              (nreverse ans))))
       (defttag nil)



       (defund ,fast-fn (names fal x yes no)
         (declare (xargs :guard (and (string-listp names)
                                     (equal fal (make-lookup-alist names))
                                     (,list-p x))))
         (cond ((atom x)
                (mv yes no))
               ((fast-memberp (,type->name (car x)) names fal)
                (,fast-fn names fal (cdr x) (cons (car x) yes) no))
               (t
                (,fast-fn names fal (cdr x) yes (cons (car x) no)))))

       (defun ,fn (names x)
         "Returns (MV NAMED UNNAMED)"
         (declare (xargs :guard (and (string-listp names)
                                     (,list-p x))
                         :verify-guards nil))
         (mbe :logic
              (mv (,keep-fn names x)
                  (,del-fn names x))
              :exec
              (b* ((fal (make-lookup-alist names))
                   ((mv yes no)
                    (,fast-fn names fal x nil nil))
                   (-   (fast-alist-free fal)))
                  (mv (reverse yes) (reverse no)))))

       (defttag vl-optimize)
       (progn!
        (set-raw-mode t)
        (setf (gethash ',fast-fn ACL2::*never-profile-ht*) t)
        (defun ,fn (names x)
          (b* ((fal (make-lookup-alist names))
               ((mv yes no)
                (,fast-fn names fal x nil nil))
               (-   (fast-alist-free fal)))
              (mv (nreverse yes) (nreverse no)))))
       (defttag nil)


       (defthm ,(mksym slow-keep-fn '-removal)
         (equal (,slow-keep-fn names x)
                (,keep-fn names x))
         :hints(("Goal" :in-theory (enable ,slow-keep-fn ,keep-fn))))

       (defthm ,(mksym fast-keep-fn '-removal)
         (implies (force (equal fal (make-lookup-alist names)))
                  (equal (,fast-keep-fn names fal x acc)
                         (revappend (,keep-fn names x) acc)))
         :hints(("Goal" :in-theory (enable ,fast-keep-fn ,keep-fn))))


       (defthm ,(mksym slow-del-fn '-removal)
         (equal (,slow-del-fn names x)
                (,del-fn names x))
         :hints(("Goal" :in-theory (enable ,slow-del-fn ,del-fn))))

       (defthm ,(mksym fast-del-fn '-removal)
         (implies (force (equal fal (make-lookup-alist names)))
                  (equal (,fast-del-fn names fal x acc)
                         (revappend (,del-fn names x) acc)))
         :hints(("Goal" :in-theory (enable ,fast-del-fn ,del-fn))))


       (defthm ,(mksym fast-fn '-removal-0)
         (implies (force (equal fal (make-lookup-alist names)))
                  (equal (mv-nth 0 (,fast-fn names fal x yes no))
                         (revappend (,keep-fn names x) yes)))
         :hints(("Goal" :in-theory (enable ,fast-fn ,keep-fn))))

       (defthm ,(mksym fast-fn '-removal-1)
         (implies (force (equal fal (make-lookup-alist names)))
                  (equal (mv-nth 1 (,fast-fn names fal x yes no))
                         (revappend (,del-fn names x) no)))
         :hints(("Goal" :in-theory (enable ,fast-fn ,del-fn))))

       (local (in-theory (enable ,keep-fn ,del-fn)))

       (verify-guards ,keep-fn)
       (verify-guards ,del-fn)
       (verify-guards ,fn)

       (defthm ,(mksym keep-fn '-when-atom)
         (implies (atom x)
                  (equal (,keep-fn names x)
                         nil)))

       (defthm ,(mksym keep-fn '-of-cons)
         (equal (,keep-fn names (cons a x))
                (if (member-equal (,type->name a) names)
                    (cons a (,keep-fn names x))
                  (,keep-fn names x))))

       (defthm ,(mksym list-p '-of- keep-fn)
         (implies (force (,list-p x))
                  (,list-p (,keep-fn names x))))

       (defthm ,(mksym 'member-equal-of- keep-fn)
         (iff (member-equal a (,keep-fn names x))
              (and (member-equal a x)
                   (member-equal (,type->name a) names))))

       (defthm ,(mksym 'subsetp-equal-of- keep-fn)
         (subsetp-equal (,keep-fn names x) x))



       (defthm ,(mksym del-fn '-when-atom)
         (implies (atom x)
                  (equal (,del-fn names x)
                         nil)))

       (defthm ,(mksym del-fn '-of-cons)
         (equal (,del-fn names (cons a x))
                (if (member-equal (,type->name a) names)
                    (,del-fn names x)
                  (cons a (,del-fn names x)))))

       (defthm ,(mksym list-p '-of- del-fn)
         (implies (force (,list-p x))
                  (,list-p (,del-fn names x))))

       (defthm ,(mksym 'member-equal-of- del-fn)
         (iff (member-equal a (,del-fn names x))
              (and (member-equal a x)
                   (not (member-equal (,type->name a) names)))))

       (defthm ,(mksym 'subsetp-equal-of- del-fn)
         (subsetp-equal (,del-fn names x) x))

       )))

(defmacro def-vl-filter-by-name (type &key
                                      (keep-long '"")
                                      (del-long '"")
                                      (filter-long '"")
                                      short-name
                                      accessor
                                      suffix)
  (let* ((mksym-package-symbol 'vl::foo)
         (short-name (or short-name "name"))
         (accessor   (or accessor (mksym 'vl- type '->name)))
         (suffix     (or suffix (mksym type 's))))
    (def-vl-filter-by-name-fn type keep-long del-long filter-long
      short-name accessor suffix)))


(def-vl-filter-by-name netdecl)
(def-vl-filter-by-name regdecl)
(def-vl-filter-by-name vardecl)
(def-vl-filter-by-name eventdecl)
(def-vl-filter-by-name portdecl)
(def-vl-filter-by-name paramdecl)
(def-vl-filter-by-name fundecl)
(def-vl-filter-by-name taskdecl)


(def-vl-filter-by-name module
  :del-long "<p>This is a low-level operation that simply removes the listed
modules.  It can be \"unsafe\" in that it can ruin the @(see completeness) of a
module list should any remaining modules instantiate the removed modules.  Some
safer, higher-level alternatives include @(see vl-remove-bad-modules), @(see
vl-remove-unnecessary-modules), and @(see vl-propagate-errors).</p>"

  :keep-long "<p><b>Note</b>: it is often better to use the related function
@(see vl-fast-find-modules).  When the list of names is short,
<tt>vl-fast-find-modules</tt> basically just requires a few hash table lookups,
whereas <tt>vl-keep-modules</tt> has to recur over the entire list of
modules.</p>")

(defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-delete-modules
  (implies (force (no-duplicatesp-equal (vl-modulelist->names mods)))
           (no-duplicatesp-equal
            (vl-modulelist->names
             (vl-delete-modules names mods))))
  :hints(("Goal" :in-theory (enable vl-delete-modules))))

(def-vl-filter-by-name modinst
  :accessor vl-modinst->modname
  :short-name "modname"
  :suffix modinsts-by-modname)

(def-vl-filter-by-name modinst
  :accessor vl-modinst->instname
  :short-name "instname"
  :suffix modinsts-by-instname)


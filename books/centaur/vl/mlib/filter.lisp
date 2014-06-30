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

(defxdoc filtering-by-name
  :parents (mlib)
  :short "Functions for filtering lists of module elements by their names."

  :long "<p>We implement functions for keeping and deleting elements by their
names, and also for partitioning lists into named and unnamed subsets.</p>

<p>Our implementations are logically simple, but we use MBE to make them fairly
efficient.  In particular, suppose we want to keep, delete, or filter the list
@('X') using some list of @('NAMES').  If there are only a few names, we use
naive algorithm that calls @('member-equal') repeatedly, and this is
effectively @('O(|X|)').</p>

<p>When there are many names, we use @(see make-lookup-alist) to construct a
temporary, fast alist, and use @(see fast-memberp) to perform the lookups.
Assuming that hashing operations are constant time, constructing this table is
@('O(|NAMES|)'), and the subsequent processing of @('X') is @('O(|X|)').</p>")

(defund def-vl-filter-by-name-fn
  (type          ;; should be 'netdecl, 'vardecl, 'module, etc.
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
         (type-fix     (mksym 'vl- type '-fix))
         (list-p       (mksym 'vl- type 'list-p))
         (list-fix     (mksym 'vl- type 'list-fix))
         (fast-fn      (mksym 'vl-fast-filter- suffix))
         (fn           (mksym 'vl-filter- suffix))
         (del-fn       (mksym 'vl-delete- suffix))
         (slow-del-fn  (mksym 'vl-slow-delete- suffix))
         (fast-del-fn  (mksym 'vl-fast-delete- suffix))
         (keep-fn      (mksym 'vl-keep- suffix))
         (slow-keep-fn (mksym 'vl-slow-keep- suffix))
         (fast-keep-fn (mksym 'vl-fast-keep- suffix))
         )
    `(encapsulate ()

       (define ,fast-keep-fn ((names string-listp)
                              (fal   (equal fal (make-lookup-alist names)))
                              (x     ,list-p)
                              nrev)
         :parents (,keep-fn)
         :hooks nil
         (if (atom x)
             (nrev-fix nrev)
           (let ((nrev (if (fast-memberp (,type->name (car x)) (string-list-fix names) fal)
                           (nrev-push (,type-fix (car x)) nrev)
                         nrev)))
             (,fast-keep-fn names fal (cdr x) nrev))))

       (define ,slow-keep-fn ((names string-listp)
                              (x     ,list-p))
         :parents (,keep-fn)
         :hooks nil
         (cond ((atom x)
                nil)
               ((member-equal (,type->name (car x)) (string-list-fix names))
                (cons (,type-fix (car x)) (,slow-keep-fn names (cdr x))))
               (t
                (,slow-keep-fn names (cdr x)))))

       (define ,keep-fn
         :parents (filtering-by-name)
         :short ,(cat "Keep @(see VL-" (symbol-name type) "-P)s by " short-name ".")
         ((names string-listp ,(cat "Names of @(see VL-" (symbol-name type) "-P)s to keep."))
          (x     ,list-p      "List to filter."))
         :long ,keep-long
         :returns (filtered-x ,list-p)
         :verify-guards nil
         (mbe :logic
              (cond ((atom x)
                     nil)
                    ((member-equal (,type->name (car x)) (string-list-fix names))
                     (cons (,type-fix (car x)) (,keep-fn names (cdr x))))
                    (t
                     (,keep-fn names (cdr x))))
              :exec
              (b* (((when (or (atom names)
                              (atom x)))
                    ;; Stupid optimization
                    nil)
                   ((unless (longer-than-p 10 names))
                    (,slow-keep-fn names x))
                   (fal (make-lookup-alist names))
                   (ans (with-local-nrev
                          (,fast-keep-fn names fal x nrev)))
                   (- (fast-alist-free fal)))
                ans))
         ///
         (defthm ,(mksym keep-fn '-when-atom)
           (implies (atom x)
                    (equal (,keep-fn names x)
                           nil)))

         (defthm ,(mksym keep-fn '-of-cons)
           (equal (,keep-fn names (cons a x))
                  (if (member-equal (,type->name a) (string-list-fix names))
                      (cons (,type-fix a) (,keep-fn names x))
                    (,keep-fn names x))))

         (defthm ,(mksym 'member-equal-of- keep-fn)
           (iff (member-equal a (,keep-fn names x))
                (and (member-equal a (,list-fix x))
                     (member-equal (,type->name a) (string-list-fix names)))))

         (defthm ,(mksym 'subsetp-equal-of- keep-fn)
           (subsetp-equal (,keep-fn names x)
                          (,list-fix x)))

         (defthm ,(mksym keep-fn '-when-atom-of-names)
           (implies (atom names)
                    (equal (,keep-fn names x)
                           nil)))

         (defthm ,(mksym slow-keep-fn '-removal)
           (equal (,slow-keep-fn names x)
                  (,keep-fn names x))
           :hints(("Goal" :in-theory (enable ,slow-keep-fn ,keep-fn))))

         (defthm ,(mksym fast-keep-fn '-removal)
           (equal (,fast-keep-fn names fal x nrev)
                  (append nrev (,keep-fn names x)))
           :hints(("Goal" :in-theory (enable ,fast-keep-fn ,keep-fn))))

         (verify-guards ,keep-fn))


       (define ,fast-del-fn ((names string-listp)
                             (fal   (equal fal (make-lookup-alist names)))
                             (x     ,list-p)
                             nrev)
         :parents (,del-fn)
         :hooks nil
         (if (atom x)
             (nrev-fix nrev)
           (let ((nrev (if (fast-memberp (,type->name (car x)) (string-list-fix names) fal)
                           nrev
                         (nrev-push (,type-fix (car x)) nrev))))
             (,fast-del-fn names fal (cdr x) nrev))))

       (define ,slow-del-fn ((names string-listp)
                             (x     ,list-p))
         :hooks nil
         (cond ((atom x)
                nil)
               ((member-equal (,type->name (car x)) (string-list-fix names))
                (,slow-del-fn names (cdr x)))
               (t
                (cons (,type-fix (car x)) (,slow-del-fn names (cdr x))))))

       (define ,del-fn
         :parents (filtering-by-name)
         :short ,(cat "Delete @(see VL-" (symbol-name type) "-P)s by " short-name ".")
         ((names string-listp ,(cat "Names of @(see VL-" (symbol-name type) "-P)s to remove."))
          (x     ,list-p      "List to filter."))
         :returns (filtered-x ,list-p)
         :long ,del-long
         :verify-guards nil
         (mbe :logic
              (cond ((atom x)
                     nil)
                    ((member-equal (,type->name (car x)) (string-list-fix names))
                     (,del-fn names (cdr x)))
                    (t
                     (cons (,type-fix (car x)) (,del-fn names (cdr x)))))
              :exec
              (b* (((when (atom names))
                    ;; Stupid optimization
                    (redundant-list-fix x))
                   ((when (atom x))
                    ;; Stupid optimization
                    nil)
                   ((unless (longer-than-p 10 names))
                    (,slow-del-fn names x))
                   (fal (make-lookup-alist names))
                   (ans (with-local-nrev
                          (,fast-del-fn names fal x nrev)))
                   (- (fast-alist-free fal)))
                ans))
         ///
         (defthm ,(mksym del-fn '-when-atom)
           (implies (atom x)
                    (equal (,del-fn names x)
                           nil)))

         (defthm ,(mksym del-fn '-of-cons)
           (equal (,del-fn names (cons a x))
                  (if (member-equal (,type->name a) (string-list-fix names))
                      (,del-fn names x)
                    (cons (,type-fix a) (,del-fn names x)))))

         (defthm ,(mksym 'member-equal-of- del-fn)
           (iff (member-equal a (,del-fn names x))
                (and (member-equal a (,list-fix x))
                     (not (member-equal (,type->name a) (string-list-fix names))))))

         (defthm ,(mksym 'subsetp-equal-of- del-fn)
           (subsetp-equal (,del-fn names x) (,list-fix x)))

         (defthm ,(mksym del-fn '-when-atom-of-names)
           (implies (atom names)
                    (equal (,del-fn names x)
                           (,list-fix (list-fix x)))))

         (defthm ,(mksym slow-del-fn '-removal)
           (equal (,slow-del-fn names x)
                  (,del-fn names x))
           :hints(("Goal" :in-theory (enable ,slow-del-fn ,del-fn))))

         (defthm ,(mksym fast-del-fn '-removal)
           (equal (,fast-del-fn names fal x nrev)
                  (append nrev (,del-fn names x)))
           :hints(("Goal" :in-theory (enable ,fast-del-fn ,del-fn))))

         (verify-guards ,del-fn))


       (define ,fast-fn ((names string-listp)
                         (fal   (equal fal (make-lookup-alist names)))
                         (x     ,list-p)
                         (nrev  "Matches")
                         (nrev2 "Non-Matches"))
         :hooks nil
         (cond ((atom x)
                (let* ((nrev (nrev-fix nrev))
                       (nrev2 (nrev-fix nrev2)))
                  (mv nrev nrev2)))
               ((fast-memberp (,type->name (car x)) (string-list-fix names) fal)
                (let ((nrev (nrev-push (,type-fix (car x)) nrev)))
                  (,fast-fn names fal (cdr x) nrev nrev2)))
               (t
                (let ((nrev2 (nrev-push (,type-fix (car x)) nrev2)))
                  (,fast-fn names fal (cdr x) nrev nrev2)))))

       (define ,fn
         :parents (filtering-by-name)
         :short ,(cat "Partition a list of @(see VL-" (symbol-name type) "-P)s by " short-name ".")
         ((names string-listp "Names to filter with.")
          (x     ,list-p      "List to filter."))
         :returns (mv named unnamed)
         :long ,(cat "<p>The only reason to use this function is efficiency.
Logically, @('named') is equal to @(see " (symbol-name keep-fn) ") and
@('unnamed') is equal to @(see " (symbol-name del-fn) ").  We leave this
function enabled and would think it odd to ever prove a theorem about it.</p>" filter-long)
         :enabled t
         :hooks nil
         :verify-guards nil
         (mbe :logic
              (mv (,keep-fn names x)
                  (,del-fn names x))
              :exec
              (b* (((when (atom names))
                    ;; Stupid optimization
                    (mv nil (redundant-list-fix x)))
                   ((when (atom x))
                    ;; Stupid optimization
                    (mv nil nil))
                   (fal (make-lookup-alist names))
                   ((local-stobjs nrev nrev2)
                    (mv yes no nrev nrev2))
                   ((mv nrev nrev2)
                    (,fast-fn names fal x nrev nrev2))
                   (- (fast-alist-free fal))
                   ((mv yes nrev) (nrev-finish nrev))
                   ((mv no nrev2) (nrev-finish nrev2)))
                (mv yes no nrev nrev2)))
         ///
         (defthm ,(mksym fast-fn '-removal-0)
           (equal (mv-nth 0 (,fast-fn names fal x nrev nrev2))
                  (append nrev (,keep-fn names x)))
           :hints(("Goal" :in-theory (enable ,fast-fn ,keep-fn))))

         (defthm ,(mksym fast-fn '-removal-1)
           (equal (mv-nth 1 (,fast-fn names fal x nrev nrev2))
                  (append nrev2 (,del-fn names x)))
           :hints(("Goal" :in-theory (enable ,fast-fn ,del-fn))))

         (local (in-theory (enable ,keep-fn ,del-fn)))

         (verify-guards ,fn))

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


;; BOZO maybe build these into fty deflist

(defthm vl-netdecllist-fix-of-list-fix
  (equal (vl-netdecllist-fix (list-fix x))
         (list-fix (vl-netdecllist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-vardecllist-fix-of-list-fix
  (equal (vl-vardecllist-fix (list-fix x))
         (list-fix (vl-vardecllist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-portdecllist-fix-of-list-fix
  (equal (vl-portdecllist-fix (list-fix x))
         (list-fix (vl-portdecllist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-paramdecllist-fix-of-list-fix
  (equal (vl-paramdecllist-fix (list-fix x))
         (list-fix (vl-paramdecllist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-fundecllist-fix-of-list-fix
  (equal (vl-fundecllist-fix (list-fix x))
         (list-fix (vl-fundecllist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-taskdecllist-fix-of-list-fix
  (equal (vl-taskdecllist-fix (list-fix x))
         (list-fix (vl-taskdecllist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-modinstlist-fix-of-list-fix
  (equal (vl-modinstlist-fix (list-fix x))
         (list-fix (vl-modinstlist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-modulelist-fix-of-list-fix
  (equal (vl-modulelist-fix (list-fix x))
         (list-fix (vl-modulelist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-udplist-fix-of-list-fix
  (equal (vl-udplist-fix (list-fix x))
         (list-fix (vl-udplist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-configlist-fix-of-list-fix
  (equal (vl-configlist-fix (list-fix x))
         (list-fix (vl-configlist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-programlist-fix-of-list-fix
  (equal (vl-programlist-fix (list-fix x))
         (list-fix (vl-programlist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-interfacelist-fix-of-list-fix
  (equal (vl-interfacelist-fix (list-fix x))
         (list-fix (vl-interfacelist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-packagelist-fix-of-list-fix
  (equal (vl-packagelist-fix (list-fix x))
         (list-fix (vl-packagelist-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-typedeflist-fix-of-list-fix
  (equal (vl-typedeflist-fix (list-fix x))
         (list-fix (vl-typedeflist-fix x)))
  :hints(("Goal" :induct (len x))))


(def-vl-filter-by-name netdecl)
(def-vl-filter-by-name vardecl)
(def-vl-filter-by-name portdecl)
(def-vl-filter-by-name paramdecl)
(def-vl-filter-by-name fundecl)
(def-vl-filter-by-name taskdecl)

(def-vl-filter-by-name modinst
  :accessor vl-modinst->modname
  :short-name "modname"
  :suffix modinsts-by-modname)

(def-vl-filter-by-name modinst
  :accessor vl-modinst->instname
  :short-name "instname"
  :suffix modinsts-by-instname)


(define vl-filter-modinsts-by-modname+ ((names string-listp)
                                        (x     vl-modinstlist-p)
                                        (fal   (equal fal (make-lookup-alist names))))
  :parents (filtering-by-name vl-filter-modinsts-by-modname)
  :short "Same as @(see vl-filter-modinsts-by-modname), but requires that the
          fast alist of @('names') be provided instead of recomputing it."
  :enabled t
  (mbe :logic (vl-filter-modinsts-by-modname names x)
       :exec (b* (((when (atom names))
                   (mv nil (redundant-list-fix x)))
                  ((when (atom x)) (mv nil nil))
                  ((local-stobjs nrev nrev2)
                   (mv yes no nrev nrev2))
                  ((mv nrev nrev2)
                   (vl-fast-filter-modinsts-by-modname names fal x nrev nrev2))
                  ((mv yes nrev) (nrev-finish nrev))
                  ((mv no nrev2) (nrev-finish nrev2)))
               (mv yes no nrev nrev2))))


(def-vl-filter-by-name module
  :del-long "<p>This is a low-level operation that simply removes the listed
modules.  It can be \"unsafe\" in that it can ruin the @(see completeness) of a
module list should any remaining modules instantiate the removed modules.  Some
safer, higher-level alternatives include @(see vl-remove-bad-modules), @(see
vl-remove-unnecessary-modules), and @(see vl-design-propagate-errors).</p>"

  :keep-long "<p><b>Note</b>: it is often better to use the related function
@(see vl-fast-find-modules).  When the list of names is short,
@('vl-fast-find-modules') basically just requires a few hash table lookups,
whereas @('vl-keep-modules') has to recur over the entire list of
modules.</p>")

(encapsulate
  ()
  (local (defthm crock
           (implies (not (member a (vl-modulelist->names mods)))
                    (not (member a (vl-modulelist->names (vl-delete-modules names mods)))))
           :hints(("Goal" :in-theory (enable vl-delete-modules)))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-delete-modules
    (implies (force (no-duplicatesp-equal (vl-modulelist->names mods)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (vl-delete-modules names mods))))
    :hints(("Goal" :in-theory (enable vl-delete-modules)))))


(def-vl-filter-by-name udp)
(def-vl-filter-by-name config)
(def-vl-filter-by-name package)
(def-vl-filter-by-name interface)
(def-vl-filter-by-name program)
(def-vl-filter-by-name typedef)



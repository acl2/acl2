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
(include-book "../mlib/filter")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(deftranssum vl-description
  :parents (loader)
  :short "Representation of an arbitrary, top-level element."
  (vl-module
   vl-udp
   vl-interface
   vl-package
   vl-program
   vl-config
   ;; bozo add bind directives

   ;; package items
   vl-netdecl
   vl-taskdecl
   vl-fundecl
   vl-paramdecl
   vl-import

   ;; bozo lots of package items are missing
   )
  :long "<p>This corresponds to the @('description') production in
SystemVerilog.  These are (the currently supported subset of) the items that
can occur at the top level of a SystemVerilog design.</p>

<p>These are a temporary structure created by the loader. Most code in VL
should never know or care about descriptions because, at the end of the loading
process, we convert all of the descriptions into a @(see vl-design-p).</p>")

(defrule tag-when-vl-description-p-forward
  ;; bozo integrate into deftranssum?
  (implies (vl-description-p x)
           (or (equal (tag x) :vl-module)
               (equal (tag x) :vl-udp)
               (equal (tag x) :vl-interface)
               (equal (tag x) :vl-package)
               (equal (tag x) :vl-program)
               (equal (tag x) :vl-config)
               (equal (tag x) :vl-netdecl)
               (equal (tag x) :vl-taskdecl)
               (equal (tag x) :vl-fundecl)
               (equal (tag x) :vl-paramdecl)
               (equal (tag x) :vl-import)
               ))
  :rule-classes ((:forward-chaining :trigger-terms ((vl-description-p x))))
  :enable vl-description-p)

(fty::deflist vl-descriptionlist :elt-type vl-description-p)

(deflist vl-descriptionlist-p (x)
  (vl-description-p x)
  :elementp-of-nil nil
  :parents (loader))

(defthm vl-descriptionlist-fix-of-list-fix
  (equal (vl-descriptionlist-fix (list-fix x))
         (list-fix (vl-descriptionlist-fix x)))
  :hints(("Goal" :induct (len x))))

(local (xdoc::set-default-parents vl-description))

(defthm vl-descriptionlist-p-when-sublist
  (and (implies (vl-modulelist-p x) (vl-descriptionlist-p x))
       (implies (vl-udplist-p x) (vl-descriptionlist-p x))
       (implies (vl-interfacelist-p x) (vl-descriptionlist-p x))
       (implies (vl-packagelist-p x) (vl-descriptionlist-p x))
       (implies (vl-programlist-p x) (vl-descriptionlist-p x))
       (implies (vl-configlist-p x) (vl-descriptionlist-p x))
       (implies (vl-netdecllist-p x) (vl-descriptionlist-p x))
       (implies (vl-taskdecllist-p x) (vl-descriptionlist-p x))
       (implies (vl-fundecllist-p x) (vl-descriptionlist-p x))
       (implies (vl-paramdecllist-p x) (vl-descriptionlist-p x))
       (implies (vl-importlist-p x) (vl-descriptionlist-p x)))
  :hints(("Goal" :induct (len x))))


(define vl-description->name ((x vl-description-p))
  :short "Get the name from most descriptions, or @('nil') if this description
doesn't introduce a name (e.g., an @('import') statement."
  :returns (name maybe-stringp :rule-classes :type-prescription)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-module->name x))
      (:vl-udp       (vl-udp->name x))
      (:vl-interface (vl-interface->name x))
      (:vl-package   (vl-package->name x))
      (:vl-program   (vl-program->name x))
      (:vl-config    (vl-config->name x))
      (:vl-netdecl   (vl-netdecl->name x))
      (:vl-taskdecl  (vl-taskdecl->name x))
      (:vl-fundecl   (vl-fundecl->name x))
      (:vl-paramdecl (vl-paramdecl->name x))
      (:vl-import    nil)
      (otherwise     (impossible)))))


(define vl-descriptionlist->names-nrev ((x vl-descriptionlist-p) nrev)
  :parents (vl-descriptionlist->names)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (name (vl-description->name (car x)))
       (nrev (if name
                 (nrev-push name nrev)
               nrev)))
    (vl-descriptionlist->names-nrev (cdr x) nrev)))

(define vl-descriptionlist->names ((x vl-descriptionlist-p))
  :short "Collect all names introduced by a @(see vl-descriptionlist-p)."
  :parents (vl-descriptionlist-p)
  :long "<p>Note that descriptions may not have names, in which case we don't
add anything.  In other words, the list of names returned may be shorter than
the number of descriptions in the list.</p>"
  :verify-guards nil
  (mbe :logic (if (consp x)
                  (if (vl-description->name (car x))
                      (cons (vl-description->name (car x))
                            (vl-descriptionlist->names (cdr x)))
                    (vl-descriptionlist->names (cdr x)))
                nil)
       :exec (with-local-nrev (vl-descriptionlist->names-nrev x nrev)))
  ///
  (defthm vl-descriptionlist->names-nrev-removal
    (equal (vl-descriptionlist->names-nrev x nrev)
           (append nrev (vl-descriptionlist->names x)))
    :hints(("Goal" :in-theory (enable vl-descriptionlist->names-nrev))))

  (verify-guards vl-descriptionlist->names)

  (defthm vl-descriptionlist->names-when-not-consp
    (implies (not (consp x))
             (equal (vl-descriptionlist->names x)
                    nil)))

  (defthm vl-descriptionlist->names-of-cons
    (equal (vl-descriptionlist->names (cons a x))
           (if (vl-description->name a)
               (cons (vl-description->name a)
                     (vl-descriptionlist->names x))
             (vl-descriptionlist->names x))))

  (defthm vl-descriptionlist->names-of-list-fix
    (equal (vl-descriptionlist->names (list-fix x))
           (vl-descriptionlist->names x)))

  (defcong list-equiv equal (vl-descriptionlist->names x) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (vl-descriptionlist->names-of-list-fix))
            :use ((:instance vl-descriptionlist->names-of-list-fix (x x))
                  (:instance vl-descriptionlist->names-of-list-fix (x acl2::x-equiv))))))

  (defthm vl-descriptionlist->names-of-append
    (equal (vl-descriptionlist->names (append x y))
           (append (vl-descriptionlist->names x)
                   (vl-descriptionlist->names y))))

  (defthm vl-descriptionlist->names-of-rev
    (equal (vl-descriptionlist->names (rev x))
           (rev (vl-descriptionlist->names x))))

  (defthm string-listp-of-vl-descriptionlist->names
    (string-listp (vl-descriptionlist->names x)))

  (defthm no-nil-in-vl-descriptionlist->names
    (not (member nil (vl-descriptionlist->names x)))))


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
  (b* (((when (atom x))
        nil)
       (x1    (vl-description-fix (car x)))
       (name1 (vl-description->name x1))
       ((unless name1)
        (vl-descalist (cdr x))))
    (hons-acons name1 x1 (vl-descalist (cdr x)))))



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
  (b* (((when (atom descs))
        nil)
       (desc1 (vl-description-fix (car descs)))
       (name1 (vl-description->name desc1))
       ((when (and name1 (equal name name1)))
        desc1))
    (vl-find-description name (cdr descs)))
  ///
  (defthm vl-find-description-when-atom
    (implies (atom descs)
             (equal (vl-find-description name descs)
                    nil)))

  (defthm vl-find-description-of-cons
    (equal (vl-find-description name (cons a x))
           (if (and (vl-description->name a)
                    (equal name (vl-description->name a)))
               (vl-description-fix a)
             (vl-find-description name x))))

  (defthm vl-find-description-of-nil
    (equal (vl-find-description nil descs)
           nil))

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

(def-vl-filter-by-name description)


(define vl-sort-descriptions ((x          vl-descriptionlist-p)
                              &key
                              (modules    vl-modulelist-p)
                              (udps       vl-udplist-p)
                              (interfaces vl-interfacelist-p)
                              (programs   vl-programlist-p)
                              (packages   vl-packagelist-p)
                              (configs    vl-configlist-p)
                              (netdecls   vl-netdecllist-p)
                              (taskdecls  vl-taskdecllist-p)
                              (fundecls   vl-fundecllist-p)
                              (paramdecls vl-paramdecllist-p)
                              (imports    vl-importlist-p))
  :returns (mv (modules    vl-modulelist-p)
               (udps       vl-udplist-p)
               (interfaces vl-interfacelist-p)
               (programs   vl-programlist-p)
               (packages   vl-packagelist-p)
               (configs    vl-configlist-p)
               (netdecls   vl-netdecllist-p)
               (taskdecls  vl-taskdecllist-p)
               (fundecls   vl-fundecllist-p)
               (paramdecls vl-paramdecllist-p)
               (imports    vl-importlist-p))
  (b* (((when (atom x))
        (mv (vl-modulelist-fix modules)
            (vl-udplist-fix udps)
            (vl-interfacelist-fix interfaces)
            (vl-programlist-fix programs)
            (vl-packagelist-fix packages)
            (vl-configlist-fix configs)
            (vl-netdecllist-fix netdecls)
            (vl-taskdecllist-fix taskdecls)
            (vl-fundecllist-fix fundecls)
            (vl-paramdecllist-fix paramdecls)
            (vl-importlist-fix imports)))
       (x1  (vl-description-fix (car x)))
       (tag (tag x1)))
    (vl-sort-descriptions
     (cdr x)
     :modules    (if (eq tag :vl-module)    (cons x1 modules)    modules)
     :udps       (if (eq tag :vl-udp)       (cons x1 udps)       udps)
     :interfaces (if (eq tag :vl-interface) (cons x1 interfaces) interfaces)
     :programs   (if (eq tag :vl-program)   (cons x1 programs)   programs)
     :packages   (if (eq tag :vl-package)   (cons x1 packages)   packages)
     :configs    (if (eq tag :vl-config)    (cons x1 configs)    configs)
     :netdecls   (if (eq tag :vl-netdecl)   (cons x1 netdecls)   netdecls)
     :taskdecls  (if (eq tag :vl-taskdecl)  (cons x1 taskdecls)  taskdecls)
     :fundecls   (if (eq tag :vl-fundecl)   (cons x1 fundecls)   fundecls)
     :paramdecls (if (eq tag :vl-paramdecl) (cons x1 paramdecls) paramdecls)
     :imports    (if (eq tag :vl-import)    (cons x1 imports)    imports))))


(define vl-design-from-descriptions ((x vl-descriptionlist-p))
  :returns (design vl-design-p)
  (b* (((mv modules udps interfaces programs packages configs netdecls taskdecls fundecls paramdecls imports)
        (vl-sort-descriptions x)))
    (make-vl-design :mods       modules
                    :udps       udps
                    :interfaces interfaces
                    :programs   programs
                    :packages   packages
                    :configs    configs
                    :netdecls   netdecls
                    :taskdecls  taskdecls
                    :fundecls   fundecls
                    :paramdecls paramdecls
                    :imports    imports)))

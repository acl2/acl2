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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "VL")
(include-book "scopestack")
(include-book "expr-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system)
                           double-containment
                           default-car default-cdr
                           natp-when-posp
                           negative-when-natp
                           integerp-when-natp
                           acl2::nfix-when-not-natp
                           nfix
                           ACL2::CAR-WHEN-ALL-EQUALP
                           acl2::cons-equal)))

(local (xdoc::set-default-parents vl-interface-mocktype))

(define vl-vardecl-mockmember ((x vl-vardecl-p))
  :returns (member vl-structmember-p)
  (b* (((vl-vardecl x)))
    (make-vl-structmember :name x.name
                          :type x.type
                          :atts x.atts)))

(defprojection vl-vardecllist-mockmembers ((x vl-vardecllist-p))
  :returns (members vl-structmemberlist-p)
  (vl-vardecl-mockmember x))

(defines vl-interface-mocktype
  :parents (mlib)
  :short "Create a datatype that corresponds to an already-elaborated
          interface."
  :long "<p>In many ways interface instances are like ordinary variables:
         they can be passed to submodules, arrays of them can be indexed
         into, etc.  In our SV conversion we want to represent the data
         associated with an interface instance in the same way as if it
         were just a structure.</p>

         <p>This is tricky because an interface is not actually a datatype,
         so we can't just reuse convenient (and complicated) functions
         like @(see vl-datatype-size) on them.  Rather than duplicate the
         code, we make a ``mock'' datatype that corresponds to the data
         portion of an interface.</p>"

  :verify-guards nil

  (define vl-interface-mocktype ((x vl-interface-p)
                                 (ss vl-scopestack-p "design level")
                                 &key ((reclimit natp) '1000))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (type (and (vl-datatype-p type)
                            (not (vl-datatype->udims type)))))
    :measure (acl2::nat-list-measure (list reclimit 10 0))
    (vl-genblob-interface-mocktype (vl-interface->genblob x) ss))

  (define vl-genblob-interface-mocktype ((x vl-genblob-p)
                                         (ss vl-scopestack-p "outside the scope")
                                         &key ((reclimit natp) 'reclimit))
    :measure (acl2::nat-list-measure (list reclimit 5 (vl-genblob-count x)))
    :returns (mv (err (iff (vl-msg-p err) err))
                 ;; Note: it's important that the type we produce has no udims,
                 ;; because we replace them below if we have an instance array
                 ;; or ifport array.
                 (type (and (vl-datatype-p type)
                            (not (vl-datatype->udims type)))))
    (b* (((vl-genblob x) (vl-genblob-fix x))
         (reclimit (lnfix reclimit))
         (ss (vl-scopestack-push x ss))
         (var-membs (vl-vardecllist-mockmembers x.vardecls))
         ((mv err1 inst-membs) (vl-modinstlist-interface-mockmembers x.modinsts ss))
         ((mv err2 gen-membs) (vl-generatelist-interface-mockmembers x.generates ss))
         ;; note: we don't need to look at regularports because they have
         ;; corresponding vardecls that we've already dealt with.
         ((mv err3 ifport-membs) (vl-interfaceportlist-mockmembers x.ifports ss))
         ;;  We have arranged the order of these structmembers to correspond to
         ;;  the aliases as they are produced in vl-genblob->svex-modules.
         ;;  This seems good in order to have a consistent view of these
         ;;  interfaces, but we're not sure it's actually necessary.
         (struct (make-vl-struct :members (append-without-guard gen-membs
                                                                ifport-membs
                                                                inst-membs
                                                                var-membs)))
         (type (if (stringp x.id)
                   (make-vl-usertype :name (vl-idscope x.id)
                                     :res struct)
                 struct)))
      (mv (vmsg-concat err1 err2 err3)
          type)))

  (define vl-interfacename-mocktype ((name stringp "name of the interface")
                                     (ss vl-scopestack-p)
                                     &key ((reclimit natp) 'reclimit))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (type (and (iff (vl-datatype-p type) type)
                            (implies type (not (vl-datatype->udims type)))
                            (implies (not err) type))))
    :measure (acl2::nat-list-measure (list reclimit 0 0))
    (b* ((reclimit (lnfix reclimit))
         ((mv mod design-ss) (vl-scopestack-find-definition/ss name ss))
         ((unless (eq (tag mod) :vl-interface))
          ;; We won't warn about this because we could have gotten the name
          ;; from a modinst.  We (should?) take care of this elsewhere for
          ;; interfaceports.
          (mv (vmsg "interfaces should only instantiate other interfaces: ~s0" (string-fix name))
              nil))
         ((when (zp reclimit))
          (mv (vmsg "Failed to size interfaces because the recursion limit ran out")
              nil)))
      (vl-interface-mocktype mod design-ss :reclimit (1- reclimit))))

  (define vl-modinst-interface-mockmember ((x vl-modinst-p)
                                           (ss vl-scopestack-p)
                                           &key ((reclimit natp) 'reclimit))
    :measure (acl2::nat-list-measure (list reclimit 3 0))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (member (and (iff (vl-structmember-p member) member)
                              (implies (not err) member))))
    (b* (((vl-modinst x) (vl-modinst-fix x))
         (reclimit (lnfix reclimit))
         ((unless x.instname)
          (mv (vmsg "~a0: Expected interface instances to be named" x)
              nil))
         ((mv err type) (vl-interfacename-mocktype x.modname ss))
         ((unless type) (mv err nil)))
      (mv err
          (make-vl-structmember
           :name x.instname
           :type (if x.range
                     (vl-datatype-update-udims (list (vl-range->dimension x.range)) type)
                   type)))))

  (define vl-modinstlist-interface-mockmembers ((x vl-modinstlist-p)
                                                (ss vl-scopestack-p)
                                                &key ((reclimit natp) 'reclimit))
    :measure (acl2::nat-list-measure (list reclimit 3 (len x)))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (members vl-structmemberlist-p))
    (b* ((reclimit (lnfix reclimit))
         ((when (atom x)) (mv nil nil))
         ((mv err1 memb1) (vl-modinst-interface-mockmember (car x) ss))
         ((mv err2 membs2) (vl-modinstlist-interface-mockmembers (cdr x) ss)))
      (mv (vmsg-concat err1 err2)
          (if memb1 (cons memb1 membs2) membs2))))

  (define vl-interfaceport-mockmember ((x vl-interfaceport-p)
                                       (ss vl-scopestack-p)
                                       &key ((reclimit natp) 'reclimit))
    :measure (acl2::nat-list-measure (list reclimit 3 0))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (member (and (iff (vl-structmember-p member) member)
                              (implies (not err) member))))
    (b* (((vl-interfaceport x) (vl-interfaceport-fix x))
         (reclimit (lnfix reclimit))
         ((mv err type) (vl-interfacename-mocktype x.ifname ss))
         ((unless type) (mv err nil)))
      (mv err
          (make-vl-structmember
           :name x.name
           :type (if x.udims
                     (vl-datatype-update-udims x.udims type)
                   type)))))

  (define vl-interfaceportlist-mockmembers ((x vl-interfaceportlist-p)
                                            (ss vl-scopestack-p)
                                            &key ((reclimit natp) 'reclimit))
    :measure (acl2::nat-list-measure (list reclimit 3 (len x)))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (members vl-structmemberlist-p))
    (b* ((reclimit (lnfix reclimit))
         ((when (atom x)) (mv nil 0))
         ((mv err1 memb1) (vl-interfaceport-mockmember (car x) ss))
         ((mv err2 membs2) (vl-interfaceportlist-mockmembers (cdr x) ss)))
      (mv (vmsg-concat err1 err2)
          (if memb1 (cons memb1 membs2) membs2))))


  (define vl-generate-interface-mockmember ((x vl-genelement-p)
                                            (ss vl-scopestack-p)
                                            &key ((reclimit natp) 'reclimit))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (member (and (iff (vl-structmember-p member) member)
                              (implies (not err) member))))
    :measure (acl2::nat-list-measure (list reclimit 5 (vl-genblob-generate-count x)))
    (b* ((x (vl-genelement-fix x))
         (reclimit (lnfix reclimit)))
      (vl-genelement-case x
        :vl-genbegin (vl-genblock-interface-mockmember x.block ss)
        :vl-genarray (b* (((unless (stringp x.name))
                           (mv (vmsg "~a0: Expected generate arrays to be named" x)
                               nil))
                          ((mv err membs) (vl-genblocklist-interface-mockmembers x.blocks ss)))
                       (mv err (make-vl-structmember
                                     :name x.name
                                     :type (make-vl-struct :members membs))))
        :otherwise (mv (vmsg "Found unexpected generate element: ~a0" x)
                       nil))))

  (define vl-generatelist-interface-mockmembers ((x vl-genelementlist-p)
                                                 (ss vl-scopestack-p)
                                                 &key ((reclimit natp) 'reclimit))
    :measure (acl2::nat-list-measure (list reclimit 5 (vl-genblob-generates-count x)))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (members vl-structmemberlist-p))
    (b* ((reclimit (lnfix reclimit))
         ((when (atom x)) (mv nil nil))
         ((mv err1 first) (vl-generate-interface-mockmember (car x) ss))
         ((mv err2 rest) (vl-generatelist-interface-mockmembers (Cdr x) ss)))
      (mv (vmsg-concat err1 err2)
          (if first (cons first rest) rest))))

  (define vl-genblock-interface-mockmember ((x vl-genblock-p)
                                            (ss vl-scopestack-p)
                                            &key ((reclimit natp) 'reclimit))
    :measure (acl2::nat-list-measure (list reclimit 5 (vl-genblob-genblock-count x)))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (member (and (iff (vl-structmember-p member) member)
                              (implies (not err) member))))
    (b* (((vl-genblock x) (vl-genblock-fix x))
         (reclimit (lnfix reclimit))
         ((unless x.name)
          (mv (vmsg "~a0: Expected generate blocks to be named" x)
              nil))
         (name (if (stringp x.name) x.name (cat "[" (intstr x.name) "]")))
         (blob (vl-sort-genelements x.elems))
         ((mv err type) (vl-genblob-interface-mocktype blob ss)))
      (mv err (make-vl-structmember :name name
                                         :type type))))

  (define vl-genblocklist-interface-mockmembers ((x vl-genblocklist-p)
                                                 (ss vl-scopestack-p)
                                                 &key ((reclimit natp) 'reclimit))
    :measure (acl2::nat-list-measure (list reclimit 5 (vl-genblob-genblocklist-count x)))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (members vl-structmemberlist-p))
    (b* ((reclimit (lnfix reclimit))
         ((when (atom x)) (mv nil 0))
         ((mv err1 first) (vl-genblock-interface-mockmember (car x) ss))
         ((mv err2 rest) (vl-genblocklist-interface-mockmembers (Cdr x) ss)))
      (mv (vmsg-concat err1 err2)
          (if first (cons first rest) rest))))
  ///
  (verify-guards vl-interface-mocktype-fn)
  (deffixequiv-mutual vl-interface-mocktype))


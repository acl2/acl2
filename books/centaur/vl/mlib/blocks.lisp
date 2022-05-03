; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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
; Original author: Jared Davis <jared@centtech.com> (VL package)
;                   Sol Swords <sswords@centtech.com> (this book)

(in-package "VL")
;; (include-book "expr-tools")
(include-book "../parsetree")
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))


(defsection genblob
  :parents (mlib)
  :short "An abstraction that is useful for processing @('generate')
constructs."

  :long "<p>The VL @(see syntax) representation for @('generate') blocks is a
relatively complicated mutual recursion; see @(see vl-genelement).</p>

<p>In some cases you may not care about the particulars of generate statements.
For instance, say you just wanted to collect up the names of all the modules
that are being instantiated by a module.  In this case, you don't care whether
the modules are instantiated inside of generate blocks or not.  But because of
the elaborate mutual recursion, properly supporting @('generate') blocks is a
hassle.</p>

<p>BOZO document def-genblob-transform and explain this stuff.</p>")

(local (xdoc::set-default-parents genblob))

(defenum vl-scopetype-p
  (:vl-module
   :vl-interface
   :vl-class
   :vl-fundecl
   :vl-taskdecl
   :vl-blockstmt
   :vl-forstmt
   :vl-foreachstmt
   :vl-design
   :vl-package
   :vl-genblock
   :vl-genarrayblock
   :vl-genarray
   :vl-anonymous-scope))







(make-event
 `(progn

    (defprod vl-genblob
      :parents (genblob)
      :short "A collection of module elements (see @(see vl-modelement)),
generates, and ports."

      :long "<p>A genblob can be made from a @(see vl-genelementlist-p) by
sorting the elements by type; see @(see vl-sort-genelements).</p>

<p>Its fields each contain the list of elements of the given type.</p>"

      (;; We have fields for all of the modelements:
       ,@(project-over-modelement-types '(__elts__ vl-__type__list-p))
       ;; And also fields for generates and ports, since these are not modelements
       (generates vl-genelementlist-p)
       (ports     vl-portlist-p)
       (scopetype vl-scopetype-p :default :vl-anonymous-scope)
       (id        vl-maybe-scopeid :rule-classes :type-prescription
                  "Name of the subscope, or index in the case of a genarrayblock."))
      :extra-binder-names (ifports)
      :tag :vl-genblob
      :layout :tree)

    (local (defun my-default-hint (fnname id clause world)
             (declare (xargs :mode :program))
             (and (eql (len (acl2::recursivep fnname t world)) 1) ;; singly recursive
                  (let* ((pool-lst (acl2::access acl2::clause-id id :pool-lst)))
                    (and (eql 0 (acl2::access acl2::clause-id id :forcing-round))
                         (cond ((not pool-lst)
                                (let ((formals (std::look-up-formals fnname world)))
                                  `(:induct (,fnname . ,formals)
                                    :in-theory (disable (:d ,fnname)))))
                               ((equal pool-lst '(1))
                                (std::expand-calls-computed-hint clause (list fnname)))))))))


    ;; (local (std::set-returnspec-default-hints
    ;;         ((my-returnspec-default-hint 'fnname acl2::id acl2::clause world))))

    (define vl-sort-genelements-aux
      :parents (vl-sort-genelements)
      ((x           vl-genelementlist-p)
       ;; Accumulators for each type of modelement
       ,@(project-over-modelement-types '(__elts__       vl-__type__list-p))
       ;; Accumulator for generates since they aren't ordinary moditems
       (generates   vl-genelementlist-p))
      :returns (mv ,@(project-over-modelement-types `(__elts__ vl-__type__list-p))
                   (generates vl-genelementlist-p))
      :hooks ((:fix :hints ((my-default-hint
                             'vl-sort-genelements-aux
                             acl2::id acl2::clause world))))
      :verbosep t
      (b* (((when (atom x))
            (mv ,@(project-over-modelement-types
                   '(rev (vl-__type__list-fix        __elts__)))
                (rev (vl-genelementlist-fix generates))))
           (xf (car x)))
        (vl-genelement-case xf
          :vl-genbase
          (b* ((x1  xf.item)
               (tag (tag x1)))
            (vl-sort-genelements-aux
             (cdr x)
             ,@(project-over-modelement-types
                '(if (eq tag :vl-__type__)       (cons x1 __elts__)       __elts__))
             generates))
          :otherwise
          (vl-sort-genelements-aux
           (cdr x) ,@(project-over-modelement-types '__elts__)
           (cons (vl-genelement-fix (car x)) generates))))
      :prepwork
      ((local (in-theory (e/d (tag-reasoning)
                              (;; just a speed hint
                               double-containment
                               set::nonempty-means-set
                               set::sets-are-true-lists
                               acl2::rev-when-not-consp
                               default-car
                               default-cdr
                               pick-a-point-subset-strategy
                               vl-genelement-p-when-member-equal-of-vl-genelementlist-p
                               ,@(project-over-modelement-types 'vl-__type__list-p-when-subsetp-equal)
                               ,@(project-over-modelement-types 'vl-modelementlist-p-when-vl-__type__list-p)
                               (:rules-of-class :type-prescription :here)
                               ))))))

    (make-event
     (let ((genelems-call `(vl-sort-genelements-aux
                            x ,@(project-over-modelement-types '__elts__)
                            generates)))
       `(progn
          ,@(project-over-modelement-types
             `(define vl-genelementlist->__elts__ ((x vl-genelementlist-p))
                :returns (__elts__ vl-__type__list-p)
                (b* (((when (atom x)) nil)
                     (x1 (car x)))
                  (vl-genelement-case x1
                    :vl-genbase
                    (if (eq (tag x1.item) :vl-__type__)
                        (cons x1.item (vl-genelementlist->__elts__ (cdr x)))
                      (vl-genelementlist->__elts__ (cdr x)))
                    :otherwise (vl-genelementlist->__elts__ (cdr x))))
                ///
                (make-event
                 (let ((n (- (len *vl-modelement-typenames*)
                             (len (member '__type__ *vl-modelement-typenames*)))))
                   `(defthm vl-sort-genelements-aux-is-vl-genelementlist->__elts__
                      (equal (mv-nth ,n ,',genelems-call)
                             (append (rev (vl-__type__list-fix __elts__))
                                     (vl-genelementlist->__elts__ x)))
                      :hints(("Goal" :induct ,',genelems-call
                              :expand (,',genelems-call)
                              :in-theory (e/d ((:i vl-sort-genelements-aux))
                                              (acl2::rev-when-not-consp
                                               append
                                               acl2::consp-of-rev
                                               tag-reasoning)
                                              (vl-__type__-p-by-tag-when-vl-modelement-p)))))))))
    
          (define vl-genelementlist->generates ((x vl-genelementlist-p))
            :returns (generates vl-genelementlist-p)
            (b* (((when (atom x)) nil)
                 (x1 (vl-genelement-fix (car x))))
              (vl-genelement-case x1
                :vl-genbase
                (vl-genelementlist->generates (cdr x))
                :otherwise (cons x1 (vl-genelementlist->generates (cdr x)))))
            ///
            (make-event
                 (let ((n (len *vl-modelement-typenames*)))
                   `(defthm vl-sort-genelements-aux-is-vl-genelementlist->generates
                      (equal (mv-nth ,n ,',genelems-call)
                             (append (rev (vl-genelementlist-fix generates))
                                     (vl-genelementlist->generates x)))
                      :hints(("Goal" :induct ,',genelems-call
                              :expand (,',genelems-call)
                              :in-theory (e/d ((:i vl-sort-genelements-aux))
                                              (acl2::rev-when-not-consp
                                               append
                                               acl2::consp-of-rev
                                               tag-reasoning)))))))))))


    (define vl-sort-genelements
      :parents (genblob)
      :short "Sort a @(see vl-genelementlist-p) to create a @(see vl-genblob)."
      ((x vl-genelementlist-p)
       &key
       ((id vl-maybe-scopeid-p) 'nil)
       ((scopetype vl-scopetype-p) ':vl-anonymous-scope))
      :returns (blob vl-genblob-p)
      (b* (((mv ,@(project-over-modelement-types '__elts__) generates)
            (vl-sort-genelements-aux x ,@(project-over-modelement-types nil) nil)))
        (make-vl-genblob
         ,@(append-over-modelement-types '(:__elts__ __elts__))
         :generates generates
         :id id
         :scopetype scopetype)))))


(define vl-genblob->ifports
  :parents (vl-genblob)
  :short "Collect just the interface ports for a genblob."
  ((x vl-genblob-p))
  :returns (ports (vl-interfaceportlist-p ports))
  (vl-collect-interface-ports (vl-genblob->ports x))
  ///
  (local (defthm vl-regularportlist-p-when-no-interface-ports
           (implies (and (not (vl-collect-interface-ports x))
                         (vl-portlist-p x))
                    (vl-regularportlist-p x))
           :hints(("Goal" :induct (len x)
                   :in-theory (enable tag-reasoning)))))

  (defthm vl-regularportlist-p-when-no-genblob->ifports
    (implies (not (vl-genblob->ifports x))
             (vl-regularportlist-p (vl-genblob->ports x)))
    :hints(("Goal" :in-theory (enable vl-genblob->ifports)))))


(defconst *vl-module/genblob-fields*
  (append '(generate port) ;; extra things that are not modelements
          (set-difference-eq
           *vl-modelement-typenames*
           ;; things in genblobs that are not in modules
           '(fwdtypedef modport letdecl))))

(defconst *vl-interface/genblob-fields*
  (append '(generate port) ;; extra things that are not modelements
          (set-difference-eq
           *vl-modelement-typenames*
           ;; things in genblobs that are not in interfaces
           '(gateinst fwdtypedef covergroup letdecl))))

(defconst *vl-class/genblob-fields*
  '(vardecl paramdecl fundecl taskdecl typedef))

(make-event
 `(define vl-module->genblob
    :short "Convert most of a module into a @(see vl-genblob)."
    ((x vl-module-p))
    :returns (genblob vl-genblob-p)
    :long "<p>Certain fields of a @(see vl-module) aren't also fields of a
@(see vl-genblob), for instance, a genblob doesn't have warnings, a name,
location information, etc.</p>

<p>But aside from these fields, most of a module can be extracted and turned
into a genblob for easy processing.  After processing the blob, the updated
fields can be reinstalled into the module using @(see vl-genblob->module).</p>"

    (b* (((vl-module x)))
      (make-vl-genblob
       :id x.name
       :scopetype :vl-module
       ,@(template-append
          '(:__elts__ x.__elts__)
          (vl-typenames-to-tmplsubsts
           *vl-module/genblob-fields*))))))

(make-event
 `(define vl-interface->genblob
    :short "Convert most of a interface into a @(see vl-genblob)."
    ((x vl-interface-p))
    :returns (genblob vl-genblob-p)
    :long "<p>Certain fields of a @(see vl-interface) aren't also fields of a
@(see vl-genblob), for instance, a genblob doesn't have warnings, a name,
location information, etc.</p>

<p>But aside from these fields, most of a interface can be extracted and turned
into a genblob for easy processing.  After processing the blob, the updated
fields can be reinstalled into the interface using @(see vl-genblob->interface).</p>"

    (b* (((vl-interface x)))
      (make-vl-genblob
       :id x.name
       :scopetype :vl-interface
       ,@(template-append
          '(:__elts__ x.__elts__)
          (vl-typenames-to-tmplsubsts
           *vl-interface/genblob-fields*))))))

(make-event
 `(define vl-class->genblob
    :short "Convert most of a class into a @(see vl-genblob)."
    ((x vl-class-p))
    :returns (genblob vl-genblob-p)
    :long "<p>Certain fields of a @(see vl-class) aren't also fields of a
@(see vl-genblob), for instance, a genblob doesn't have warnings, a name,
location information, etc.</p>

<p>But aside from these fields, most of a class can be extracted and turned
into a genblob for easy processing.  After processing the blob, the updated
fields can be reinstalled into the class using @(see vl-genblob->class).</p>"

    (b* (((vl-class x)))
      (make-vl-genblob
       :id x.name
       :scopetype :vl-class
       ,@(template-append
          '(:__elts__ x.__elts__)
          (vl-typenames-to-tmplsubsts
           *vl-class/genblob-fields*))))))

(define vl-genblock->genblob ((x vl-genblock-p))
  :short "Convert a @(see vl-genblock) into a @(see vl-genblob)."
  :returns (blob vl-genblob-p)
  (b* (((vl-genblock x)))
    (vl-sort-genelements x.elems
                         :scopetype :vl-genblock
                         :id x.name)))


(defconst *vl-package/genblob-fields*
  '(fundecl
    taskdecl
    typedef
    paramdecl
    vardecl
    import))

(make-event
 `(define vl-package->genblob
    :short "Convert most of a package into a @(see vl-genblob)."
    ((x vl-package-p))
    :returns (genblob vl-genblob-p)
    :long "<p>Certain fields of a @(see vl-package) aren't also fields of a
@(see vl-genblob), for instance, a genblob doesn't have warnings, a name,
location information, etc.</p>

<p>But aside from these fields, most of a package can be extracted and turned
into a genblob for easy processing.  After processing the blob, the updated
fields can be reinstalled into the package using @(see vl-genblob->package).</p>"

    (b* (((vl-package x)))
      (make-vl-genblob
       :id x.name
       :scopetype :vl-package
       ,@(template-append
          '(:__elts__ x.__elts__)
          (vl-typenames-to-tmplsubsts
           *vl-package/genblob-fields*))))))



(make-event
 `(define vl-genblob->module
    :short "Install fields from a @(see vl-genblob) into a module."
    ((x vl-genblob-p)
     (orig vl-module-p))
    :returns (new-mod vl-module-p)
    :long "<p>See @(see vl-module->genblob).  This is the companion operation
which takes the fields from the genblob and sticks them back into a module.</p>

<p>Certain fields of the module, like its warnings, name, and location
information, aren't affected.  But the real fields like modinsts, assigns,
etc., are overwritten with whatever is in the genblob.</p>"

    (b* (((vl-genblob x)))
      (change-vl-module orig
                        ,@(template-append
                           '(:__elts__ x.__elts__)
                           (vl-typenames-to-tmplsubsts
                            *vl-module/genblob-fields*))))))

(make-event
 `(define vl-genblob->class
    :short "Install fields from a @(see vl-genblob) into a class."
    ((x vl-genblob-p)
     (orig vl-class-p))
    :returns (new-mod vl-class-p)
    :long "<p>See @(see vl-class->genblob).  This is the companion operation
which takes the fields from the genblob and sticks them back into a class.</p>

<p>Certain fields of the class, like its warnings, name, and location
information, aren't affected.  But the real fields like modinsts, assigns,
etc., are overwritten with whatever is in the genblob.</p>"

    (b* (((vl-genblob x)))
      (change-vl-class orig
                        ,@(template-append
                           '(:__elts__ x.__elts__)
                           (vl-typenames-to-tmplsubsts
                            *vl-class/genblob-fields*))))))

(make-event
 `(define vl-genblob->interface
    :short "Install fields from a @(see vl-genblob) into a interface."
    ((x vl-genblob-p)
     (orig vl-interface-p))
    :returns (new-mod vl-interface-p)
    :long "<p>See @(see vl-interface->genblob).  This is the companion operation
which takes the fields from the genblob and sticks them back into a interface.</p>

<p>Certain fields of the interface, like its warnings, name, and location
information, aren't affected.  But the real fields like modinsts, assigns,
etc., are overwritten with whatever is in the genblob.</p>"

    (b* (((vl-genblob x)))
      (change-vl-interface orig
                           ,@(template-append
                              '(:__elts__ x.__elts__)
                              (vl-typenames-to-tmplsubsts
                               *vl-interface/genblob-fields*))))))


(make-event
 `(define vl-genblob->package
    :short "Install fields from a @(see vl-genblob) into a package."
    ((x vl-genblob-p)
     (orig vl-package-p))
    :returns (new-mod vl-package-p)
    :long "<p>See @(see vl-package->genblob).  This is the companion operation
which takes the fields from the genblob and sticks them back into a package.</p>

<p>Certain fields of the package, like its warnings, name, and location
information, aren't affected.  But the real fields like modinsts, assigns,
etc., are overwritten with whatever is in the genblob.</p>"

    (b* (((vl-genblob x)))
      (change-vl-package orig
                           ,@(template-append
                              '(:__elts__ x.__elts__)
                              (vl-typenames-to-tmplsubsts
                               *vl-package/genblob-fields*))))))


(make-event
 `(define vl-genblob->elems-aux
    :parents (vl-genblob->elems)
    ((orig-elements vl-genelementlist-p)
     ,@(project-over-modelement-types '(__elts__ vl-__type__list-p))
     (generates vl-genelementlist-p)
     (acc vl-genelementlist-p))
    :measure (len orig-elements)
    :returns (final-acc vl-genelementlist-p)
    :prepwork ((local (in-theory (disable acl2::true-listp-append
                                          acl2::consp-of-append
                                          acl2::subsetp-append1
                                          append
                                          acl2::append-when-not-consp
                                          ,@(project-over-modelement-types
                                             'vl-__type__list-p-of-append)))))
    :hooks nil
    (b* (((when (atom orig-elements))
          (revappend-without-guard
           (vl-genelementlist-fix acc)
           (append-without-guard
            (vl-modelementlist->genelements
             (append-without-guard
              ,@(project-over-modelement-types '__elts__)))
            (vl-genelementlist-fix generates))))
         (x (car orig-elements)))
      (vl-genelement-case x
        :vl-genbase
        (case (tag x.item)
          ,@(project-over-modelement-types
             `(:vl-__type__ (b* (((mv acc __elts__)
                                  (if (consp __elts__)
                                      (mv (cons (make-vl-genbase :item (vl-__type__-fix (car __elts__))) acc)
                                          (cdr __elts__))
                                    (mv acc __elts__))))
                              (vl-genblob->elems-aux
                               (cdr orig-elements)
                               ,@(project-over-modelement-types '__elts__)
                               generates
                               acc)))))
        :otherwise (b* (((mv acc generates)
                         (if (consp generates)
                             (mv (cons (car generates) acc)
                                 (cdr generates))
                           (mv acc generates))))
                     (vl-genblob->elems-aux
                      (cdr orig-elements)
                      ,@(project-over-modelement-types '__elts__)
                      generates
                      acc))))))

(make-event
 `(define vl-genblob->elems
    ((x vl-genblob-p "the current genblob of elements")
     (orig-elements vl-genelementlist-p
                    "the original elements, used to determine the ordering of the
                     current elements will be sorted"))
    :returns (new-elements vl-genelementlist-p "flattened list of elements from genblob")
    (b* (((vl-genblob x)))
      (vl-genblob->elems-aux
       (vl-genelementlist-fix orig-elements)
       ,@(project-over-modelement-types 'x.__elts__)
       x.generates nil))))


(defthm vl-genelementlist-count-of-append
  (equal (vl-genelementlist-count (append x y))
         (+ -1 (vl-genelementlist-count x)
            (vl-genelementlist-count y)))
  :hints(("Goal" :in-theory (enable vl-genelementlist-count))))

(defthm vl-genelementlist-count-of-rev
  (equal (vl-genelementlist-count (rev x))
         (vl-genelementlist-count x))
  :hints(("Goal" :induct (len x)
          :expand ((vl-genelementlist-count x) (rev x)
                   (:free (x y) (vl-genelementlist-count (cons x y)))))))

(make-event
 `(defthm vl-genelementlist-count-of-vl-sort-genelements-aux
    (b* (((mv ,@(project-over-modelement-types '?__elts__1) generates1)
          (vl-sort-genelements-aux
           x ,@(project-over-modelement-types '__elts__) generates)))
      (<= (vl-genelementlist-count generates1)
          (+ -1 (vl-genelementlist-count x)
             (vl-genelementlist-count generates))))
    :hints(("Goal" :induct (vl-sort-genelements-aux
                            x ,@(project-over-modelement-types '__elts__) generates)
            :in-theory (e/d ((:i vl-sort-genelements-aux)
                             vl-genelementlist-count)
                            (not))
            :expand ((vl-sort-genelements-aux
                      x ,@(project-over-modelement-types '__elts__) generates))))
    :rule-classes :linear))

(defthm vl-genelementlist-count-of-vl-genelementlist-generates
  (<= (vl-genelementlist-count (vl-genelementlist->generates x))
      (vl-genelementlist-count x))
  :hints (("goal" :in-theory (enable vl-genelementlist->generates)
           :induct (len x)
           :expand ((vl-genelementlist-count x)
                    (:free (x y) (vl-genelementlist-count (cons x y))))))
  :rule-classes :linear)

(defthm vl-genelementlist-count-of-vl-sort-genelements
  (<= (vl-genelementlist-count
       (vl-genblob->generates
        (vl-sort-genelements x :id name :scopetype type)))
      (vl-genelementlist-count x))
  :hints(("Goal" :in-theory (enable vl-sort-genelements)))
  :rule-classes :linear)

;; (define vl-genelements-remove-genbases ((x vl-genelementlist-p))
;;   :returns (new-x vl-genelementlist-p)
;;   (if (atom x)
;;       nil
;;     (if (eq (vl-genelement-kind (car x)) :vl-genbase)
;;         (vl-genelements-remove-genbases (cdr x))
;;       (cons (vl-genelement-fix (car x))
;;             (vl-genelements-remove-genbases (cdr x)))))
;;   ///
;;   (defret vl-genelementlist-count-of-remove-genbases
;;     (<= (vl-genelementlist-count new-x)
;;         (vl-genelementlist-count x))
;;     :hints(("Goal" :in-theory (enable vl-genelementlist-count)))
;;     :rule-classes :linear)

;;   ()

(defines vl-genblob-count
  :parents (vl-genblob)

  (define vl-genblob-count ((x vl-genblob-p))
    :measure (two-nats-measure (vl-genelementlist-count (vl-genblob->generates x)) 9)
    :hints (("goal" :expand ((vl-sort-genelements (list x))
                             (vl-sort-genelements nil))
             ;; need hints for funky case in vl-genblob-generate-count where we
             ;; deal with a genbase by sorting its single element into a
             ;; genblob
             :in-theory (enable vl-sort-genelements-aux)))
    :returns (count posp :rule-classes :type-prescription)
    (+ 1 (vl-genblob-generates-count (vl-genblob->generates x)))
    ///
    (defret vl-genblob-count-greater-than-generates
      (< (vl-genblob-generates-count (vl-genblob->generates x))
         count)
      :rule-classes :linear)
    (defthm vl-genblob-count-of-sort-genelements-normalize
      (implies (syntaxp (or (not (equal name ''nil))
                            (not (equal scopetype '':vl-anonymous-scope))))
               (equal (vl-genblob-count (vl-sort-genelements x
                                                             :id name
                                                             :scopetype scopetype))
                      (vl-genblob-count (vl-sort-genelements x))))
      :hints (("goal"
               :in-theory (enable vl-sort-genelements)))))

  (define vl-genblob-generates-count ((x vl-genelementlist-p))
    :measure (two-nats-measure (vl-genelementlist-count x) 5)
    :returns (count posp :rule-classes :type-prescription)
    (if (atom x)
        1
      (+ 1
         (vl-genblob-generate-count (car x))
         (vl-genblob-generates-count (cdr x))))
    ///
    (defret vl-genblob-generates-count-greater-than-first
      (implies (consp x)
               (< (vl-genblob-generate-count (car x))
                  count))
      :rule-classes :linear)
    (defret vl-genblob-generates-count-gte-rest
      (<= (vl-genblob-generates-count (cdr x))
          count)
      :rule-classes :linear)
    (defret vl-genblob-generates-count-greater-than-rest
      (implies (consp x)
               (< (vl-genblob-generates-count (cdr x))
                  count))
      :rule-classes :linear))

  (define vl-genblob-genblock-count ((x vl-genblock-p))
    :measure (two-nats-measure (vl-genblock-count x) 0)
    :returns (count posp :rule-classes :type-prescription)
    (b* (((vl-genblock x)))
      (+ 2 (vl-genblob-count (vl-sort-genelements x.elems))))
    ///
    (defret vl-genblob-genblock-count-greater-than-sorted
      (< (vl-genblob-count (vl-sort-genelements (vl-genblock->elems x)
                                                :id name
                                                :scopetype type))
         (vl-genblob-genblock-count x))
      :rule-classes :linear))

  (define vl-genblob-generate-count ((x vl-genelement-p))
    :measure (two-nats-measure (vl-genelement-count x) 18)
    :returns (count posp :rule-classes :type-prescription)
    (vl-genelement-case x
      :vl-genbase (+ 2 (vl-genblob-elementlist-count (list x)))
      :vl-genbegin (+ 2 (vl-genblob-genblock-count x.block))
      :vl-genif (+ 1
                   (vl-genblob-genblock-count x.then)
                   (vl-genblob-genblock-count x.else))
      :vl-gencase (+ 1
                     (vl-genblob-genblock-count x.default)
                     (vl-genblob-gencaselist-count x.cases))
      :vl-genloop (+ 2 (vl-genblob-genblock-count x.body))
      :vl-genarray (+ 2 (vl-genblob-genblocklist-count x.blocks)))
    ///
    (defret vl-genblob-generate-count-greater-than-genbegin-block
      (implies (vl-genelement-case x :vl-genbegin)
               (< (vl-genblob-genblock-count (vl-genbegin->block x))
                  count))
      :rule-classes :linear)
    (defret vl-genblob-generate-count-greater-than-genblockarray-blocks
      (implies (vl-genelement-case x :vl-genarray)
               (< (vl-genblob-genblocklist-count (vl-genarray->blocks x))
                  count))
      :rule-classes :linear)
    (defret vl-genblob-generate-count-greater-than-genif-blocks
      (implies (vl-genelement-case x :vl-genif)
               (< (+ (vl-genblob-genblock-count (vl-genif->then x))
                     (vl-genblob-genblock-count (vl-genif->else x)))
                  count))
      :rule-classes :linear)
    (defret vl-genblob-generate-count-greater-than-gencase-blocks
      (implies (vl-genelement-case x :vl-gencase)
               (< (+ (vl-genblob-genblock-count (vl-gencase->default x))
                     (vl-genblob-gencaselist-count (vl-gencase->cases x)))
                  count))
      :rule-classes :linear)
    (defret vl-genblob-generate-count-greater-than-genloop-blocks
      (implies (vl-genelement-case x :vl-genloop)
               (< (vl-genblob-genblock-count (vl-genloop->body x))
                  count))
      :rule-classes :linear)

    (defret vl-genblob-generate-count-greater-than-genbase-item
      (implies (vl-genelement-case x :vl-genbase)
               (< (vl-genblob-elementlist-count (list x))
                  count))
      :rule-classes :linear))

  (define vl-genblob-gencaselist-count ((x vl-gencaselist-p))
    :measure (two-nats-measure (vl-gencaselist-count x) 10)
    :returns (count posp :rule-classes :type-prescription)
    (b* ((x (vl-gencaselist-fix x))
         ((when (atom x)) 1))
      (+ 1
         (vl-genblob-genblock-count (cdar x))
         (vl-genblob-gencaselist-count (cdr x))))
    ///
    (defret vl-genblob-gencaselist-count-greater-than-first
      (implies (consp (vl-gencaselist-fix x))
               (< (vl-genblob-genblock-count (cdar (vl-gencaselist-fix x)))
                  count))
      :hints (("goal" :expand ((vl-genblob-gencaselist-count x))))
      :rule-classes :linear)
    (defret vl-genblob-gencaselist-count-gte-rest
      (<= (vl-genblob-gencaselist-count (cdr (vl-gencaselist-fix x)))
          count)
      :hints (("goal" :expand ((vl-genblob-gencaselist-count x))))
      :rule-classes :linear)
    (defret vl-genblob-gencaselist-count-greater-than-rest
      (implies (consp (vl-gencaselist-fix x))
               (< (vl-genblob-gencaselist-count (cdr (vl-gencaselist-fix x)))
                  count))
      :hints (("goal" :expand ((vl-genblob-gencaselist-count x))))
      :rule-classes :linear))

  (define vl-genblob-elementlist-count ((x vl-genelementlist-p))
    :measure (two-nats-measure
              (vl-genelementlist-count
               (vl-genblob->generates (vl-sort-genelements x))) 15)
    :returns (count posp :rule-classes :type-prescription)
    (+ 1 (vl-genblob-count (vl-sort-genelements x)))
    ///
    (defret vl-genblob-elementlist-count-greater-than-genblob-count
      (< (vl-genblob-count (vl-sort-genelements x))
         count)
      :rule-classes :linear))

  (define vl-genblob-genblocklist-count ((x vl-genblocklist-p))
    :measure (two-nats-measure (vl-genblocklist-count x) 10)
    :returns (count posp :rule-classes :type-prescription)
    (if (atom x)
        1
      (+ 1
         (vl-genblob-genblock-count (car x))
         (vl-genblob-genblocklist-count (cdr x))))
    ///
    (defret vl-genblob-genblocklist-count-greater-than-first
      (implies (consp x)
               (< (vl-genblob-genblock-count (car x))
                  count))
      :rule-classes :linear)
    (defret vl-genblob-genblocklist-count-gte-rest
      (<= (vl-genblob-genblocklist-count (cdr x))
          count)
      :rule-classes :linear)
    (defret vl-genblob-genblocklist-count-greater-than-rest
      (implies (consp x)
               (< (vl-genblob-genblocklist-count (cdr x))
                  count))
      :rule-classes :linear))
  ///
  (deffixequiv-mutual vl-genblob-count))


;; Example def-genblob-transform:

;; (def-genblob-transform my-transform (;; implicitly,
;;                                      ;; (x vl-genblob-p)
;;                                      (ss vl-scopestack-p)
;;                                      (warnings vl-warninglist-p))
;;   :returns (mv (okp booleanp :rule-classes :type-prescription)
;;                (warnings vl-warninglist-p)
;;                ;; implicitly,
;;                ;; (new-x vl-genblob-p)
;;                )
;;   :apply-to-generates my-transform-on-generates
;;   (b* (((vl-genblob x))
;;        (ss (vl-scopstack-push (vl-genblob-fix x) ss))
;;        ((mv okp1 warnings new-assigns) (vl-transform-assigns x.assigns ss warnings))
;;        ((mv okp2 warnings new-generates) (my-transform-on-generates x.generates ss warnings))
;;        (res (change-vl-genblob x :assigns new-assigns :generates new-generates)))
;;     (mv (and okp1 okp2) warnings res))
;;   :combine-bindings ((okp (and okp1 okp2)))
;;   :empty-list-bindings ((okp t))
;;   :bad-generate-bindings ((okp nil)))

(program)
(set-state-ok t)
(defun formals->fixes (names formals fty-table wrld)
  (declare (xargs :mode :program))
  (b* (((when (atom names)) nil)
       (first (fty::find-formal-by-name (car names) formals))
       (type (fty::fixequiv-type-from-guard (std::formal->guard first) wrld))
       (fixtype (fty::find-fixtype-for-pred type fty-table)))
    (if fixtype
        (cons `(,(car names) (,(fty::fixtype->fix fixtype) ,(car names)))
              (formals->fixes (cdr names) formals fty-table wrld))
      (formals->fixes (cdr names) formals fty-table wrld))))



(defconst *def-genblob-transform-keywords*
  '(:apply-to-generates
    :returns
    :combine-bindings
    :empty-list-bindings
    :genblock-bindings
    :return-from-genblock-bindings
    :genarray-bindings
    :return-from-genarray-bindings
    :genif-bindings
    :return-from-genif-bindings
    :gencase-bindings
    :return-from-gencase-bindings
    :genloop-bindings
    :return-from-genloop-bindings
    ;; :elementlist-bindings
    :verify-guards
    :guard-hints
    :defines-args
    :global-extra-decls
    :no-new-x))

(defun kwd-alist->filtered-key-args (kwd-alist omit-names)
  (if (atom kwd-alist)
      nil
    (if (member (caar kwd-alist) omit-names)
        (kwd-alist->filtered-key-args (cdr kwd-alist) omit-names)
      (cons (caar kwd-alist)
            (cons (cdar kwd-alist)
                  (kwd-alist->filtered-key-args (cdr kwd-alist) omit-names))))))

(defun suffix-syms (names suffix std::mksym-package-symbol)
  (if (atom names)
      nil
    (cons (std::mksym (car names) suffix)
          (suffix-syms (cdr names) suffix std::mksym-package-symbol))))

(defun maybe-mv-fn (args)
  (if (eql (len args) 1)
      (car args)
    (cons 'mv args)))

(defmacro maybe-mv (&rest args)
  (maybe-mv-fn args))

(acl2::def-b*-binder maybe-mv
  :body
  `(b* ((,(if (eql (len acl2::args) 1)
              (car acl2::args)
            (cons 'mv acl2::args))
         ,@acl2::forms))
     ,acl2::rest-expr))


(defun def-genblob-transform-fn (name    ;; name of main function
                                 args
                                 state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((__function__ 'def-genblob-transform)
       (std::mksym-package-symbol name)
       (wrld (w state))
       ((unless (symbolp name))
        (raise "Expected a symbol for the name of the main function, not ~x0" name))
       ((mv main-stuff rest-events) (std::split-/// name args))
       ((mv kwd-alist normal-defun-stuff)
        (std::extract-keywords name (append *def-genblob-transform-keywords* std::*define-keywords*)
                          main-stuff nil))
       (raw-formals            (car normal-defun-stuff))
       (traditional-decls/docs (butlast (cdr normal-defun-stuff) 1))
       (body                   (car (last normal-defun-stuff)))

       ((getargs (apply-to-generates (std::mksym name '-generates))
                 returns
                 combine-bindings
                 empty-list-bindings
                 genblock-bindings
                 return-from-genblock-bindings
                 genarray-bindings
                 return-from-genarray-bindings
                 genif-bindings
                 return-from-genif-bindings
                 gencase-bindings
                 return-from-gencase-bindings
                 genloop-bindings
                 return-from-genloop-bindings
                 defines-args
                 ;; elementlist-bindings
                 ;; return-from-elementlist-bindings
                 (verify-guards t)
                 guard-hints
                 global-extra-decls
                 no-new-x)
        kwd-alist)

       (new-x (not no-new-x))

       (define-keys (kwd-alist->filtered-key-args
                     kwd-alist *def-genblob-transform-keywords*))

       (formal-infos (std::parse-formals name raw-formals nil wrld))
       (formal-names (std::formallist->names formal-infos))
       (return-infos (std::parse-returnspecs-aux name returns wrld))
       (return-names (std::returnspeclist->names return-infos))
       ((when (member 'x formal-names))
        (raise "X shouldn't be among the formals -- it's implicit."))
       ((when (or (member 'x return-names)
                  (member 'new-x return-names)))
        (raise "X or NEW-X shouldn't be among the returns -- it's implicit."))
       (accumulators (intersection-eq return-names formal-names))
       ;; return names need to come first so that we preserve their order and
       ;; the return-names-ordered check doesn't fail

       (?extra-formals (set-difference-eq formal-names accumulators))
       (extra-returns (set-difference-eq return-names accumulators))

       (apply-to-generate          (std::mksym name '-generate))
       (apply-to-genblock          (std::mksym name '-genblock))
       (apply-to-genblocklist (std::mksym name '-genblocklist))
       (apply-to-gencaselist       (std::mksym name '-gencaselist))

       (return-names-ordered (append extra-returns accumulators))

       ((unless (equal return-names-ordered return-names))
        (raise "Return names must be ordered so that all non-accumulators precede all accumulators"))

       (return-names1 (append (suffix-syms extra-returns '|1| std::mksym-package-symbol) accumulators))
       (return-names2 (append (suffix-syms extra-returns '|2| std::mksym-package-symbol) accumulators))
       (acc-fix-bindings (formals->fixes accumulators formal-infos (fty::get-fixtypes-alist wrld) wrld)))
    `(defines ,name
       ,@defines-args

       (define ,name ((x vl-genblob-p) . ,raw-formals)
         ;; This function is essentially provided by the user. It explains how
         ;; to transform an arbitrary genblob into a new genblob.
         :returns ,(maybe-mv-fn `(,@returns
                                  ,@(and new-x '((new-x vl-genblob-p)))))
         :measure (vl-genblob-count x)
         :verify-guards nil
         ,@define-keys
         ,@traditional-decls/docs
         ,@global-extra-decls
         ,body)

       ;; The rest of this stuff just applies the above function to translate
       ;; everything in a generate, recursively, with some special places where
       ;; you can stick in some new bindings.

       (define ,apply-to-generates ((x vl-genelementlist-p) . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  ,@(and new-x '((new-x vl-genelementlist-p)))))
         :measure (vl-genblob-generates-count x)
         ,@global-extra-decls
         (b* (((when (atom x))
               (b* (,@acc-fix-bindings
                    ,@empty-list-bindings)
                 (maybe-mv ,@return-names ,@(and new-x '(nil)))))
              ((maybe-mv ,@return-names1 ,@(and new-x '(first)))
               (,apply-to-generate (car x) . ,formal-names))
              ((maybe-mv ,@return-names2 ,@(and new-x '(rest)))
               (,apply-to-generates (cdr x) . ,formal-names))
              . ,combine-bindings)
           (maybe-mv ,@return-names
                     ;; We should be able to use append here, but ACL2 won't
                     ;; always infer the type prescription so we can run into
                     ;; guard violations.  Just use append-without-guard so
                     ;; we don't have to worry about it.
                     ,@(and new-x '((append-without-guard first rest))))))

       (define ,apply-to-genblock ((x vl-genblock-p) . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  ,@(and new-x '((new-x vl-genblock-p)))))
         :measure (vl-genblob-genblock-count x)
         ,@global-extra-decls
         (b* (,@genblock-bindings
              ((vl-genblock x))
              ((maybe-mv ,@return-names ,@(and new-x '(new-blob)))
               (,name (vl-sort-genelements x.elems
                                           :scopetype :vl-genblock
                                           :id x.name)
                      . ,formal-names))
              ,@return-from-genblock-bindings)
           (maybe-mv ,@return-names
                     ,@(and new-x '((change-vl-genblock x :elems
                                                        (vl-genblob->elems
                                                         new-blob x.elems)))))))

       (define ,apply-to-generate ((x vl-genelement-p) . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  ,@(and new-x '((new-x vl-genelementlist-p)))))
         :measure (vl-genblob-generate-count x)
         ;; Apply the user's function to a single generate.  Note that we are
         ;; given a single genelement, but we return a list(!) of genelements.
         ;;
         ;; This is basically a hack to deal with the single :vl-genbase case.
         ;; In this case, we only have a single element, but the user has given
         ;; us a function that transforms whole genblobs.  To use their function
         ;; we need a goofy hack:
         ;;
         ;;   1. turn the single element into a genblob.
         ;;   2. transform the genblob using the user's function.
         ;;   3. flatten the genblob back into the replacement.
         ;;
         ;; These flattened elements should be then be spliced back into
         ;; whatever generate scope we're processing in order to form the
         ;; replacement for our current element.
         ,@global-extra-decls
         (vl-genelement-case x

           :vl-genbase
           (b* (,@genblock-bindings
                (xlist (list x))
                ((maybe-mv ,@return-names ,@(and new-x '(new-blob)))
                 (,name (vl-sort-genelements xlist) . ,formal-names))
                ,@return-from-genblock-bindings)
             (maybe-mv ,@return-names
                       ,@(and new-x '((vl-genblob->elems new-blob xlist)))))

           :vl-genbegin
           (b* (((maybe-mv ,@return-names ,@(and new-x '(new-block)))
                 (,apply-to-genblock x.block . ,formal-names)))
             (maybe-mv ,@return-names
                       ,@(and new-x '((list (change-vl-genbegin x :block new-block))))))

           :vl-genif
           (b* (,@genif-bindings
                ((maybe-mv ,@return-names1 ,@(and new-x '(new-then)))
                 (,apply-to-genblock x.then . ,formal-names))
                ((maybe-mv ,@return-names2 ,@(and new-x '(new-else)))
                 (,apply-to-genblock x.else . ,formal-names))
                ,@return-from-genif-bindings
                . ,combine-bindings
                )
             (maybe-mv ,@return-names
                       ,@(and new-x '((list (change-vl-genif x
                                                             :then new-then
                                                             :else new-else))))))

           :vl-genarray
           (b* (,@genarray-bindings
                ((maybe-mv ,@return-names ,@(and new-x '(new-blocks)))
                 (,apply-to-genblocklist x.blocks . ,formal-names))
                ,@return-from-genarray-bindings)
             (maybe-mv ,@return-names
                       ,@(and new-x '((list (change-vl-genarray x :blocks new-blocks))))))

           :vl-genloop
           (b* (,@genloop-bindings
                ((maybe-mv ,@return-names ,@(and new-x '(new-body)))
                 (,apply-to-genblock x.body . ,formal-names))
                ,@return-from-genloop-bindings)
             (maybe-mv ,@return-names
                       ,@(and new-x '((list (change-vl-genloop x :body new-body))))))

           :vl-gencase
           (b* (,@gencase-bindings
                ((maybe-mv ,@return-names1 ,@(and new-x '(new-cases)))
                 (,apply-to-gencaselist x.cases . ,formal-names))
                ((maybe-mv ,@return-names2 ,@(and new-x '(new-default)))
                 (,apply-to-genblock x.default . ,formal-names))
                ,@return-from-gencase-bindings
                . ,combine-bindings)
             (maybe-mv ,@return-names
                       ,@(and new-x '((list (change-vl-gencase x
                                              :cases new-cases
                                              :default new-default))))))))

       (define ,apply-to-gencaselist ((x vl-gencaselist-p) . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  ,@(and new-x '((new-x vl-gencaselist-p)))))
         :measure (vl-genblob-gencaselist-count x)
         ,@global-extra-decls
         (b* ((x (vl-gencaselist-fix x))
              ((when (atom x))
               (b* (,@acc-fix-bindings
                    ,@empty-list-bindings)
                 (maybe-mv ,@return-names ,@(and new-x '(nil)))))
              ((maybe-mv ,@return-names1 ,@(and new-x '(first)))
               (,apply-to-genblock (cdar x) . ,formal-names))
              ((maybe-mv ,@return-names2 ,@(and new-x '(rest)))
               (,apply-to-gencaselist (cdr x) . ,formal-names))
              . ,combine-bindings)
           (maybe-mv ,@return-names ,@(and new-x '((cons (cons (caar x) first) rest))))))

       ;; (define ,apply-to-elementlist ((x vl-genelementlist-p) . ,raw-formals)
       ;;   :returns ,(maybe-mv-fn `(,@returns
       ;;                            ,@(and new-x '((new-x vl-genelementlist-p)))))
       ;;   :measure (vl-genblob-elementlist-count x)
       ;;   ,@global-extra-decls
       ;;   (b* (,@elementlist-bindings
       ;;        ((maybe-mv ,@return-names ,@(and new-x '(new-blob)))
       ;;         (,name (vl-sort-genelements x) . ,formal-names))
       ;;        ,@return-from-elementlist-bindings)
       ;;     (maybe-mv ,@return-names ,@(and new-x '((vl-genblob->elems new-blob x))))))

       (define ,apply-to-genblocklist ((x vl-genblocklist-p)
                                            . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  ,@(and new-x '((new-x vl-genblocklist-p)))))
         :measure (vl-genblob-genblocklist-count x)
         ,@global-extra-decls
         (b* (((when (atom x))
               (b* (,@acc-fix-bindings
                    ,@empty-list-bindings)
                 (maybe-mv ,@return-names ,@(and new-x '(nil)))))
              ((maybe-mv ,@return-names1 ,@(and new-x '(first)))
               (,apply-to-genblock (car x) . ,formal-names))
              ((maybe-mv ,@return-names2 ,@(and new-x '(rest)))
               (,apply-to-genblocklist (cdr x) . ,formal-names))
              . ,combine-bindings)
           (maybe-mv ,@return-names ,@(and new-x '((cons first rest))))))
       ///
       (local (in-theory (disable ,apply-to-genblock
                                ,apply-to-genblocklist
                                ,apply-to-gencaselist
                                ;;,apply-to-elementlist
                                ,apply-to-generate
                                ,apply-to-generates
                                ,name)))
       ,@(and verify-guards `((verify-guards ,name :hints ,guard-hints)))
       (deffixequiv-mutual ,name
         :hints ((and stable-under-simplificationp
                      (flag::expand-calls-computed-hint
                       clause '(,apply-to-genblock
                                ,apply-to-gencaselist
                                ,apply-to-genblocklist
                                ;;,apply-to-elementlist
                                ,apply-to-generate
                                ,apply-to-generates
                                ,name)))))
       ,@rest-events)))

(defmacro def-genblob-transform (name &rest args)
  `(make-event
    (def-genblob-transform-fn ',name ',args state)))

(logic)

(local
 ;; Just a test to make sure the macro is working for a simple case.
 (def-genblob-transform vl-genblob-delete-modinsts ((warnings vl-warninglist-p)
                                                    (ctx acl2::any-p))
   :returns ((warnings vl-warninglist-p))
   (b* (((vl-genblob x))
        (warnings (if x.modinsts
                      (warn :type :vl-has-modinsts
                            :msg "~a0: Deleted modinsts!"
                            :args (list ctx)
                            :fn __function__)
                    (ok)))
        ((mv warnings generates) (vl-generates-delete-modinsts x.generates warnings ctx)))
     (mv warnings (change-vl-genblob x :modinsts nil :generates generates)))
   :apply-to-generates vl-generates-delete-modinsts))


(local
 ;; Try to catch any problems with non-accumulator variables
 (def-genblob-transform vl-genblob-delete-modinsts2 ((warnings vl-warninglist-p)
                                                     (ctx acl2::any-p))
   :returns ((okp booleanp :rule-classes :type-prescription)
             (warnings vl-warninglist-p))
   (b* (((vl-genblob x))
        (okp1 (if x.modinsts nil t))
        (warnings (if x.modinsts
                      (warn :type :vl-has-modinsts
                            :msg "~a0: Deleted modinsts!"
                            :args (list ctx)
                            :fn __function__)
                    (ok)))
        ((mv okp2 warnings generates) (vl-generates-delete-modinsts2 x.generates warnings ctx)))
     (mv (and okp1 okp2)
         warnings (change-vl-genblob x :modinsts nil :generates generates)))
   :apply-to-generates vl-generates-delete-modinsts2
   :empty-list-bindings ((okp t))
   :combine-bindings ((okp (and okp1 okp2)))))


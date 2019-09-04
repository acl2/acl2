

(in-package "SV")

(include-book "centaur/sv/mods/svmods" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/substrp" :dir :system)

(include-book "svex-simplify")
(include-book "xdoc/topics" :dir :system)

;; Tool 1: Write a function to check equivalance of two designs,
;; return t even when
;; modules are in different order.
(progn
  (defun mod-alist-equiv$ (keys modalist1 modalist2)
    (if (atom keys)
        t
      (and (equal (assoc-equal (car keys)
                               modalist1)
                  (assoc-equal (car keys)
                               modalist2))
           (mod-alist-equiv$ (cdr keys)
                             modalist1
                             modalist2))))

  (defun design-equiv$ (design1 design2)
    (b* ((design1 (design-fix design1))
         (design2 (design-fix design2))
         (modalist1 (design->modalist design1))
         (modalist2 (design->modalist design2))
         (keys1 (strip-cars modalist1))
         (keys2 (strip-cars modalist2)))
      (and (or (equal (set-difference-equal keys1 keys2) nil)
               (equal (set-difference-equal keys2 keys1) nil)
               (cw "These keys are absent in the second design: ~p0 ~%"
                   (set-difference-equal keys1 keys2))
               (cw "And these keys are new in the second design: ~p0 ~%"
                   (set-difference-equal keys2 keys1)))
           (equal (design->top design1)
                  (design->top design2))
           (mod-alist-equiv$ keys2
                             modalist1
                             modalist2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tool 2: Get rid of genarray instances.

(progn

  (define genarray-modname-to-string
    ((modname modname-p))
    :verify-guards nil
    (case-match modname
      ((':genarray x)
       x)
      ((':genarray x . rest)
       (concatenate 'string
                    (if (integerp x)
                        (str::intstr x)
                      x)
                    " "
                    (genarray-modname-to-string rest)))
      ((':genblock x)
       (if (integerp x)
           (str::intstr x)
         x))
      ((':genblock x . rest)
       (concatenate 'string
                    (if (integerp x)
                        (str::intstr x)
                      x)
                    " "
                    (genarray-modname-to-string rest)))
      (&
       (hard-error 'genarray-modname-to-string
                   "Unexpected genarray modname ~p0 ~%"
                   (list (cons #\0 modname))))))

  (define flatten-genarray-var ((var)
                                (trace string-listp))
    :verify-guards nil
    (case-match var
      ((':var (':address name & depth) . y)
       (let ((res `(:var ,(concatenate 'string (nth depth trace) name) . ,y)))
         (case-match res
           ((':var name . '0) name)
           (& res))))
      ((':var (inst . sig) . y)
       `(:var (,(concatenate 'string (nth 0 trace) inst) . ,sig) . ,y))
      ((':var name . y)
       `(:var ,(concatenate 'string (nth 0 trace) name) . ,y))
      (&
       (concatenate 'string (nth 0 trace) var))))

  (define flatten-genarray-search-var ((term)
                                       (trace string-listp))
    :verify-guards nil
    (cond ((stringp term)
           (flatten-genarray-var term trace))
          ((atom term)
           term)
          ((equal (car term) :var)
           (flatten-genarray-var term trace))
          (t
           (cons (flatten-genarray-search-var (car term) trace)
                 (flatten-genarray-search-var (cdr term) trace)))))

  ;; (assign trace
  ;;         (list
  ;;          (genarray-modname-to-string
  ;;           '(:GENARRAY "partial_product_muxes"
  ;;                       :GENBLOCK 1  :GENBLOCK "genblk1"))
  ;;          (genarray-modname-to-string
  ;;           '(:GENARRAY "partial_product_muxes"
  ;;                       :GENBLOCK 1))
  ;;          (genarray-modname-to-string
  ;;           '(:GENARRAY "partial_product_muxes"))
  ;;          ""))

  ;; (flatten-genarray-search-var
  ;;  (module->wires
  ;;   (cdr (assoc-equal '("booth2_multiplier_signed_64x32_97"
  ;;                       :GENARRAY "partial_product_muxes"
  ;;                       :GENBLOCK 1  :GENBLOCK "genblk1")
  ;;                     (design->modalist
  ;;                      svl::*big-sv-design*))))
  ;;  (@ trace))

  (defun genarray-create-trace (mod-name)
    (if (atom mod-name)
        (list "")
      (cons (genarray-modname-to-string mod-name)
            (genarray-create-trace (take (- (len mod-name) 2) mod-name)))))

  (defines sv-mod-remove-genarray

    (define flatten-genarray-mod ((modname modname-p)
                                  (modalist modalist-p)
                                  (visited-mods modnamelist-p)
                                  (limit natp))
      (declare (xargs :measure (nfix limit)))
      :verify-guards nil
      :guard (consp modname)
      (cond
       ((zp limit)
        (progn$
         (hard-error 'sv-design-remove-genarray
                     "Limit reached! ~%" nil)
         (mv nil nil nil nil nil)))
       (t
        (b* (#|(suffix (genarray-modname-to-string (cdr modname)))
             (trace (cons suffix trace))||#
             (trace (genarray-create-trace (cdr modname)))
             ((sv::module module) (cdr (assoc-equal modname modalist)))
             (new-wires (flatten-genarray-search-var module.wires trace))
             (new-assigns (flatten-genarray-search-var module.assigns trace))
             (new-aliaspaires (flatten-genarray-search-var module.aliaspairs trace))
             ((mv all-other-mods other-new-aliaspairs
                  all-insts other-new-assigns other-new-wires)
              (sv-insts-remove-genarray modname module.insts  modalist
                                        visited-mods  (1- limit))))
          (mv all-other-mods
              (append new-aliaspaires other-new-aliaspairs)
              all-insts
              (append new-assigns other-new-assigns)
              (append new-wires other-new-wires))))))

    (define sv-insts-remove-genarray ((modname modname-p)
                                      (insts modinstlist-p)
                                      (modalist modalist-p)
                                      (visited-mods modnamelist-p)
                                      (limit natp))
      (declare (xargs :measure (nfix limit)))
      (cond
       ((zp limit)
        (progn$
         (hard-error 'sv-design-remove-genarray
                     "Limit reached! ~%" nil)
         (mv nil nil nil nil nil)))
       ((atom insts)
        (mv nil nil nil nil nil))
       (t
        (b* ((inst (if (and (consp modname)
                            (atom (modinst->modname (car insts)))
                            (atom (modinst->instname (car insts)))
                            (not (str::substrp " " (modinst->instname (car insts)))))
                       (let ((res (change-modinst
                                   (car insts)
                                   :instname
                                   (concatenate
                                    'string
                                    (genarray-modname-to-string (cdr modname))
                                    (if (integerp (modinst->instname (car
                                                                      insts)))
                                        (str::intstr (modinst->instname (car
                                                                         insts)))
                                      (modinst->instname (car insts)))))))
                         (progn$
                          #|(cw "Here in=~p0, out=~p1 ~%" (car insts)
                          res)||#
                          res))
                     (car insts)))
             ((sv::modinst inst) inst)
             (is-genarray (case-match inst.modname
                            ((& :genarray . &) t)
                            (& nil)))
             ((mv other-modules
                  new-aliaspaires this-insts
                  new-assigns new-wires)
              (if is-genarray
                  (flatten-genarray-mod inst.modname
                                        modalist visited-mods (1- limit))
                (mv nil nil inst nil nil)))
             (other-modules
              (cond ((and (not is-genarray)
                          (atom inst.modname)
                          (not (member-equal inst.modname visited-mods)))
                     (sv-mod-remove-genarray
                      inst.modname
                      (cdr (assoc-equal inst.modname modalist))
                      modalist
                      visited-mods
                      (1- limit)))
                    (t
                     other-modules)))
             (visited-mods
              (append (strip-cars other-modules) visited-mods))
             ((mv rest-other-modules rest-new-alispairs
                  rest-insts rest-new-assigns rest-new-wires)
              (sv-insts-remove-genarray modname
                                        (if is-genarray
                                            (append (cdr insts)
                                                    this-insts)
                                          (cdr insts))
                                        modalist
                                        visited-mods
                                        (1- limit))))
          (mv (append other-modules
                      rest-other-modules)
              (append new-aliaspaires
                      rest-new-alispairs)
              (cond (is-genarray rest-insts)
                    ((consp inst.modname)
                     (progn$
                      (cw "Warning: This module name ~p0 is not
                                    atom. Skipping.. ~%"
                          inst.modname)
                      rest-insts))
                    (t
                     (cons-with-hint this-insts rest-insts insts)))
              (append new-assigns
                      rest-new-assigns)
              (append new-wires
                      rest-new-wires))))))

    (define sv-mod-remove-genarray
      ((modname modname-p)
       (module module-p)
       (modalist modalist-p)
       (visited-mods modnamelist-p)
       (limit natp))
      (declare (xargs :measure (nfix limit)))
      (declare (ignorable visited-mods))
      (if (zp limit)
          (progn$
           (hard-error 'sv-design-remove-genarray
                       "Limit reached! ~%" nil)
           nil)
        (b* (((mv all-other-modules new-aliaspairs
                  all-insts new-assigns new-wires)
              (sv-insts-remove-genarray  modname
                                         (module->insts module)
                                         modalist
                                         (cons modname visited-mods)
                                         (1- limit))))
          (acons
           modname
           (change-module
            module
            :wires (append new-wires (module->wires module))
            :insts all-insts
            :assigns (append new-assigns (module->assigns module))
            :aliaspairs (append new-aliaspairs (module->aliaspairs module)))
           all-other-modules)))))

  (define sv-design-remove-genarray ((design design-p))
    (declare (xargs :mode :program))
    :verify-guards nil
    (change-design
     design
     :modalist
     (sv-mod-remove-genarray
      (design->top design)
      (cdr (assoc-equal (design->top design)
                        (design->modalist design)))
      (design->modalist design)
      nil
      (expt 2 50)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tool 3: Simplify svexes in assignments.

(encapsulate
  nil

  (defttag t)
  (set-register-invariant-risk nil)
  (defttag nil)
  
  (define get-total-lhs-w ((lhs lhs-p))
    (if (atom lhs)
        0
      (+ (lhrange->w (car lhs))
         (get-total-lhs-w (cdr lhs)))))

  (define insert-partsel-to-svexes ((assigns assigns-p))
    :guard-hints (("Goal"
                   :in-theory (e/d (svex-p) ())))
    (if (atom assigns)
        nil
      (b* ((lhs (caar assigns))
           (total-lhs-w (get-total-lhs-w lhs))
           ((driver d) (cdar assigns)))
        (cons (cons lhs (change-driver d
                                       :value `(partsel 0 ,total-lhs-w
                                                        ,d.value)))
              (insert-partsel-to-svexes (cdr assigns))))))

  (define insert-partsel-to-svexes-and-simplify ((assigns assigns-p)
                                                 (state state-p)
                                                 (rp::rp-state rp::rp-statep)
                                                 (created-rules))
    :guard-hints (("Goal"
                   :in-theory (e/d (svex-p) ())))
    (declare (xargs :mode :program))
    #|:returns (mv (res assigns-p :hyp (assigns-p assigns))
    (rp::rp-state rp-state))||#
    (if (atom assigns)
        (mv nil rp::rp-state)
      (b* ((lhs (caar assigns))
           (total-lhs-w (get-total-lhs-w lhs))
           ((driver d) (cdar assigns))
           ((mv svex-res rp::rp-state)
            (svl::svex-simplify `(partsel 0 ,total-lhs-w ,d.value)
                                :created-rules created-rules))
           ((mv rest rp::rp-state)
            (insert-partsel-to-svexes-and-simplify (cdr assigns) state
                                                   rp::rp-state created-rules)))
        (mv (cons (cons lhs (change-driver d :value svex-res))
                  rest)
            rp::rp-state))))

  (define sv-mods-simplify-svexes ((modalist modalist-p)
                                   (state state-p)
                                   (rp::rp-state rp::rp-statep)
                                   (created-rules))
    (declare (xargs :mode :program))
    (if (atom modalist)
        (mv nil rp::rp-state)
      (b* (((mv rest rp::rp-state)
            (sv-mods-simplify-svexes (cdr modalist) state rp::rp-state
                                     created-rules))
           ((mv cur rp::rp-state)
            (insert-partsel-to-svexes-and-simplify
             (module->assigns (cdar modalist))
             state rp::rp-state created-rules)))
        (mv (acons (caar modalist)
                   (change-module (cdar modalist) :assigns cur)
                   rest)
            rp::rp-state))))


   
  
  (define sv-design-simplify-svexes ((design design-p)
                                     (state state-p)
                                     (rp::rp-state rp::rp-statep))
    (declare (xargs :mode :program))
    "Using the rewrite rules in the current theory, go through all the ~
assignments and simplify them in an sv-design, using the function svl::svex-simplify."
    (b* ((created-rules (svl::svex-rw-create-rules))
         ((mv new-modalist rp::rp-state) (sv-mods-simplify-svexes
                                          (design->modalist design)
                                          state rp::rp-state created-rules)))
      (mv (change-design design :modalist new-modalist)
          rp::rp-state))))



(acl2::defxdoc sv-design-simplify-svexes
  :parents (projects/svl)
  :short "Apply @('svl::svex-simplify') to all the assignments in a sv design.")

(in-theory (disable acl2::natp-when-gte-0
                    acl2::natp-when-integerp))

#|

(DESIGN-EQUIV$
(sv-design-remove-genarray svl::*booth-sv-design*)
svl::*booth-sv-design*)

(DESIGN-EQUIV$
(sv-design-remove-genarray svl::*counter-sv-design*)
svl::*counter-sv-design*)

(DESIGN-EQUIV$
(sv-design-remove-genarray svl::*mult-sv-design*)
svl::*mult-sv-design*)

(DESIGN-EQUIV$
(sv-design-remove-genarray svl::*signed64-sv-design*)
svl::*signed64-sv-design*)

(DESIGN-EQUIV$
(sv-design-remove-genarray svl::*signed128-sv-design*)
svl::*signed128-sv-design*)

(DESIGN-EQUIV$
(sv-design-remove-genarray svl::*big-sv-design*)
svl::*big-sv-design*)
||#

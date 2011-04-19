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
(include-book "parse-statements")
(include-book "parse-ports")      ;; vl-portdecllist-p, vl-portlist-p
(include-book "parse-nets")       ;; vl-assignlist-p, vl-netdecllist-p
(include-book "parse-blockitems") ;; vl-vardecllist-p, vl-regdecllist-p, vl-eventdecllist-p, vl-paramdecllist-p
(include-book "parse-insts")      ;; vl-modinstlist-p
(include-book "parse-gates")      ;; vl-gateinstlist-p
(local (include-book "../util/arithmetic"))




;                            MODULE CONSTRUCTION
;
; Our parsing functions return all kinds of different module items.  We need to
; go ahead and sort these into the different buckets we're going to use.

(defund vl-moduleitem-p (x)
  (declare (xargs :guard t))
  (or (vl-portdecl-p x)
      (vl-assign-p x)
      (vl-netdecl-p x)
      (vl-vardecl-p x)
      (vl-regdecl-p x)
      (vl-eventdecl-p x)
      (vl-paramdecl-p x)
      (vl-modinst-p x)
      (vl-gateinst-p x)
      (vl-always-p x)
      (vl-initial-p x)))

(defthm vl-moduleitem-p-forward-to-consp
  (implies (vl-moduleitem-p x)
           (consp x))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable vl-moduleitem-p))))

(deflist vl-moduleitemlist-p (x)
  (vl-moduleitem-p x)
  :elementp-of-nil nil)

(encapsulate
 ()
 (local (in-theory (enable vl-moduleitem-p)))

 (defthm vl-moduleitemlist-p-when-vl-portdecllist-p
   (implies (vl-portdecllist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x))))

 (defthm vl-moduleitemlist-p-when-vl-assignlist-p
   (implies (vl-assignlist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x))))

 (defthm vl-moduleitemlist-p-when-vl-netdecllist-p
   (implies (vl-netdecllist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x))))

 (defthm vl-moduleitemlist-p-when-vl-vardecllist-p
   (implies (vl-vardecllist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x))))

 (defthm vl-moduleitemlist-p-when-vl-regdecllist-p
   (implies (vl-regdecllist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x))))

 (defthm vl-moduleitemlist-p-when-vl-eventdecllist-p
   (implies (vl-eventdecllist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x))))

 (defthm vl-moduleitemlist-p-when-vl-paramdecllist-p
   (implies (vl-paramdecllist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x))))

 (defthm vl-moduleitemlist-p-when-vl-modinstlist-p
   (implies (vl-modinstlist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x))))

 (defthm vl-moduleitemlist-p-when-vl-gateinstlist-p
   (implies (vl-gateinstlist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x))))

 (defthm vl-moduleitemlist-p-when-vl-alwayslist-p
   (implies (vl-alwayslist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x))))

 (defthm vl-moduleitemlist-p-when-vl-initiallist-p
   (implies (vl-initiallist-p x)
            (vl-moduleitemlist-p x))
   :hints(("Goal" :induct (len x)))))




(defsection discriminate-moduleitems-by-tag

  (local (in-theory (enable vl-moduleitem-p)))

  (defthm vl-portdecl-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-portdecl)
                  (vl-moduleitem-p x))
             (vl-portdecl-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm vl-assign-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-assign)
                  (vl-moduleitem-p x))
             (vl-assign-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm vl-netdecl-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-netdecl)
                  (vl-moduleitem-p x))
             (vl-netdecl-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm vl-vardecl-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-vardecl)
                  (vl-moduleitem-p x))
             (vl-vardecl-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm vl-regdecl-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-regdecl)
                  (vl-moduleitem-p x))
             (vl-regdecl-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm vl-eventdecl-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-eventdecl)
                  (vl-moduleitem-p x))
             (vl-eventdecl-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm vl-paramdecl-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-paramdecl)
                  (vl-moduleitem-p x))
             (vl-paramdecl-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm vl-modinst-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-modinst)
                  (vl-moduleitem-p x))
             (vl-modinst-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm vl-gateinst-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-gateinst)
                  (vl-moduleitem-p x))
             (vl-gateinst-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm vl-always-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-always)
                  (vl-moduleitem-p x))
             (vl-always-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm vl-initial-p-by-tag-when-vl-moduleitem-p
    (implies (and (equal (tag x) :vl-initial)
                  (vl-moduleitem-p x))
             (vl-initial-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))))



(defund vl-sort-module-items (x portdecls assigns netdecls vardecls regdecls
                                eventdecls paramdecls modinsts gateinsts
                                alwayses initials)
  (declare (xargs :guard (and (vl-moduleitemlist-p x)
                              (vl-portdecllist-p portdecls)
                              (vl-assignlist-p assigns)
                              (vl-netdecllist-p netdecls)
                              (vl-vardecllist-p vardecls)
                              (vl-regdecllist-p regdecls)
                              (vl-eventdecllist-p eventdecls)
                              (vl-paramdecllist-p paramdecls)
                              (vl-modinstlist-p modinsts)
                              (vl-gateinstlist-p gateinsts)
                              (vl-alwayslist-p alwayses)
                              (vl-initiallist-p initials)
                              (true-listp portdecls)
                              (true-listp assigns)
                              (true-listp netdecls)
                              (true-listp vardecls)
                              (true-listp regdecls)
                              (true-listp eventdecls)
                              (true-listp paramdecls)
                              (true-listp modinsts)
                              (true-listp gateinsts)
                              (true-listp alwayses)
                              (true-listp initials))))
  (if (atom x)
      (mv (reverse portdecls)
          (reverse assigns)
          (reverse netdecls)
          (reverse vardecls)
          (reverse regdecls)
          (reverse eventdecls)
          (reverse paramdecls)
          (reverse modinsts)
          (reverse gateinsts)
          (reverse alwayses)
          (reverse initials))
    (let ((tag (tag (car x))))
      (vl-sort-module-items (cdr x)
                            (if (eq tag :vl-portdecl)  (cons (car x) portdecls)  portdecls)
                            (if (eq tag :vl-assign)    (cons (car x) assigns)    assigns)
                            (if (eq tag :vl-netdecl)   (cons (car x) netdecls)   netdecls)
                            (if (eq tag :vl-vardecl)   (cons (car x) vardecls)   vardecls)
                            (if (eq tag :vl-regdecl)   (cons (car x) regdecls)   regdecls)
                            (if (eq tag :vl-eventdecl) (cons (car x) eventdecls) eventdecls)
                            (if (eq tag :vl-paramdecl) (cons (car x) paramdecls) paramdecls)
                            (if (eq tag :vl-modinst)   (cons (car x) modinsts)   modinsts)
                            (if (eq tag :vl-gateinst)  (cons (car x) gateinsts)  gateinsts)
                            (if (eq tag :vl-always)    (cons (car x) alwayses)   alwayses)
                            (if (eq tag :vl-initial)   (cons (car x) initials)   initials)
                            ))))


(defsection vl-sort-module-items-types

  (local (in-theory (enable vl-sort-module-items)))

  (defmacro vl-sort-module-items$ ()
    `(vl-sort-module-items x portdecls assigns netdecls vardecls regdecls
                           eventdecls paramdecls modinsts gateinsts
                           alwayses initials))

  (defthm vl-portdecllist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-portdecllist-p portdecls)
                  (true-listp portdecls))
             (vl-portdecllist-p (mv-nth 0 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$))))

  (defthm vl-assignlist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-assignlist-p assigns)
                  (true-listp assigns))
             (vl-assignlist-p (mv-nth 1 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$))))

  (defthm vl-netdecllist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-netdecllist-p netdecls)
                  (true-listp netdecls))
             (vl-netdecllist-p (mv-nth 2 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$))))

  (defthm vl-vardecllist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-vardecllist-p vardecls)
                  (true-listp vardecls))
             (vl-vardecllist-p (mv-nth 3 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$))))

  (defthm vl-regdecllist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-regdecllist-p regdecls)
                  (true-listp regdecls))
             (vl-regdecllist-p (mv-nth 4 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$))))

  (defthm vl-eventdecllist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-eventdecllist-p eventdecls)
                  (true-listp eventdecls))
             (vl-eventdecllist-p (mv-nth 5 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$))))

  (defthm vl-paramdecllist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-paramdecllist-p paramdecls)
                  (true-listp paramdecls))
             (vl-paramdecllist-p (mv-nth 6 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$))))

  (defthm vl-modinstlist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-modinstlist-p modinsts)
                  (true-listp modinsts))
             (vl-modinstlist-p (mv-nth 7 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$))))

  (defthm vl-gateinstlist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-gateinstlist-p gateinsts)
                  (true-listp gateinsts))
             (vl-gateinstlist-p (mv-nth 8 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$))))

  (defthm vl-alwayslist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-alwayslist-p alwayses)
                  (true-listp alwayses))
             (vl-alwayslist-p (mv-nth 9 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$))))

  (defthm vl-initiallist-p-of-vl-sort-module-items
    (implies (and (vl-moduleitemlist-p x)
                  (vl-initiallist-p initials)
                  (true-listp initials))
             (vl-initiallist-p (mv-nth 10 (vl-sort-module-items$))))
    :hints(("Goal" :induct (vl-sort-module-items$)))))


(defund vl-make-module-by-items (name params ports items atts minloc maxloc warnings)
  (declare (xargs :guard (and (stringp name)
                              ;; BOZO add something about params
                              (vl-portlist-p ports)
                              (vl-moduleitemlist-p items)
                              (vl-atts-p atts)
                              (vl-location-p minloc)
                              (vl-location-p maxloc)
                              (vl-warninglist-p warnings)
                              )))
  (mv-let (portdecls assigns netdecls vardecls regdecls eventdecls paramdecls
                     modinsts gateinsts alwayses initials)
          (vl-sort-module-items items nil nil nil nil nil nil nil nil nil nil nil)
          (make-vl-module :name name
                          :params params
                          :ports ports
                          :portdecls portdecls
                          :assigns assigns
                          :netdecls netdecls
                          :vardecls vardecls
                          :regdecls regdecls
                          :eventdecls eventdecls
                          :paramdecls paramdecls
                          :modinsts modinsts
                          :gateinsts gateinsts
                          :alwayses alwayses
                          :initials initials
                          :atts atts
                          :minloc minloc
                          :maxloc maxloc
                          :warnings warnings
                          :origname name
                          :comments nil
                          )))

(defthm vl-module-p-of-vl-make-module-by-items
  (implies (and (force (stringp name))
                ;; BOZO add something about params
                (force (vl-portlist-p ports))
                (force (vl-moduleitemlist-p items))
                (force (vl-atts-p atts))
                (force (vl-location-p minloc))
                (force (vl-location-p maxloc))
                (force (vl-warninglist-p warnings)))
           (vl-module-p (vl-make-module-by-items name params ports items atts minloc maxloc warnings)))
  :hints(("Goal" :in-theory (enable vl-make-module-by-items))))








(defparser vl-parse-initial-construct (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-initiallist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-initial))
        (stmt := (vl-parse-statement))
        (return (list (make-vl-initial :loc (vl-token->loc kwd)
                                       :stmt stmt
                                       :atts atts)))))

(defparser vl-parse-always-construct (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-alwayslist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-always))
        (stmt := (vl-parse-statement))
        (return (list (make-vl-always :loc (vl-token->loc kwd)
                                      :stmt stmt
                                      :atts atts)))))








;                           UNIMPLEMENTED PRODUCTIONS
;
; Eventually we may implement some more of these.  For now, we just cause
; an error if any of them is used.
;
; BOZO consider changing some of these to be in the task declaration style,
; so that if they are used we give a warning and then gracefully skip over
; them.
;

(defparser vl-parse-generate-region (tokens warnings)
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (vl-unimplemented))

(defparser vl-parse-specify-block (tokens warnings)
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (vl-unimplemented))

(defparser vl-parse-specparam-declaration (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))

(defparser vl-parse-genvar-declaration (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))


(defund vl-task-p (x)
  (declare (xargs :guard t))
  ;; BOZO horrible hack for task declaration skipping
  (not x))




(defparser vl-parse-task-declaration-aux (tokens warnings)
  ;; BOZO this is really not implemented.  We just read until endtask, throwing
  ;; away any tokens we encounter until then.
  :result (vl-task-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endtask)
          (:= (vl-match-token :vl-kwd-endtask))
          (return nil))
        (:s= (vl-match-any))
        (:= (vl-parse-task-declaration-aux))
        (return nil)))

(encapsulate
 ()
 (local (defthm horrible-hack-1
          (implies (vl-task-p x)
                   (vl-moduleitemlist-p x))
          :hints(("Goal" :in-theory (enable vl-task-p)))))

 (local (defthm horrible-hack-2
          (implies (and (not (mv-nth 0 (vl-parse-task-declaration-aux tokens)))
                        (force (vl-tokenlist-p tokens)))
                   (vl-moduleitemlist-p (mv-nth 1 (vl-parse-task-declaration-aux tokens))))))

 (defparser vl-parse-task-declaration (atts tokens warnings)
   :guard (vl-atts-p atts)
   :result (vl-moduleitemlist-p val)
   :resultp-of-nil t
   :true-listp t
   :fails gracefully
   :count strong
   (declare (ignore atts))
   (if (not (consp tokens))
       (vl-parse-error "Unexpected EOF.")
     (seqw tokens warnings
           (:= (vl-parse-warning :vl-warn-taskdecl
                                 (str::cat "Task declarations are not yet implemented.  "
                                           "Instead, we are simply ignoring everything "
                                           "until 'endtask'.")))
           (ret := (vl-parse-task-declaration-aux))
           (return ret)))))



(defparser vl-parse-function-declaration-aux (tokens warnings)
  ;; BOZO this is really not implemented.  We just read until endfunction, throwing
  ;; away any tokens we encounter until then.
  :result (vl-task-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endfunction)
          (:= (vl-match-token :vl-kwd-endfunction))
          (return nil))
        (:s= (vl-match-any))
        (:= (vl-parse-function-declaration-aux))
        (return nil)))

(encapsulate
 ()
 (local (defthm horrible-hack-1
          (implies (vl-task-p x)
                   (vl-moduleitemlist-p x))
          :hints(("Goal" :in-theory (enable vl-task-p)))))

 (local (defthm horrible-hack-2
          (implies (and (not (mv-nth 0 (vl-parse-function-declaration-aux tokens)))
                        (force (vl-tokenlist-p tokens)))
                   (vl-moduleitemlist-p (mv-nth 1 (vl-parse-function-declaration-aux tokens))))))

 (defparser vl-parse-function-declaration (atts tokens warnings)
   :guard (vl-atts-p atts)
   :result (vl-moduleitemlist-p val)
   :resultp-of-nil t
   :true-listp t
   :fails gracefully
   :count strong
   (declare (ignore atts))
   (if (atom tokens)
       (vl-parse-error "Unexpected EOF.")
     (seqw tokens warnings
           (:= (vl-parse-warning :vl-warn-function
                                 (str::cat "Function declarations are not yet implemented.  "
                                           "Instead, we are simply ignoring everything until "
                                           "'endfunction'.")))
           (ret := (vl-parse-function-declaration-aux))
           (return ret)))))

(defparser vl-parse-parameter-override (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))

(defparser vl-parse-loop-generate-construct (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))

(defparser vl-parse-conditional-generate-construct (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))







;                                 MODULE ITEMS
;
; Note below that I have flattened out module_or_generate_item_declaration
; below.  Also note that port_declarations also begin with
; {attribute_instance}, so really the only module items that can't have
; attributes are generate_region and specify_block.
;
; module_item ::=                                             ;; STARTS WITH
;    port_declaration ';'                                     ;; a direction
;  | non_port_module_item                                     ;;
;                                                             ;;
; non_port_module_item ::=                                    ;;
;    module_or_generate_item                                  ;;
;  | generate_region                                          ;; 'generate'
;  | specify_block                                            ;; 'specify'
;  | {attribute_instance} parameter_declaration ';'           ;; 'parameter'
;  | {attribute_instance} specparam_declaration               ;; 'specparam'
;                                                             ;;
; module_or_generate_item ::=                                 ;;
;    {attribute_instance} net_declaration                     ;; [see below]
;  | {attribute_instance} reg_declaration                     ;; 'reg'
;  | {attribute_instance} integer_declaration                 ;; 'integer'
;  | {attribute_instance} real_declaration                    ;; 'real'
;  | {attribute_instance} time_declaration                    ;; 'time'
;  | {attribute_instance} realtime_declaration                ;; 'realtime'
;  | {attribute_instance} event_declaration                   ;; 'event'
;  | {attribute_instance} genvar_declaration                  ;; 'genvar'
;  | {attribute_instance} task_declaration                    ;; 'task'
;  | {attribute_instance} function_declaration                ;; 'function'
;  | {attribute_instance} local_parameter_declaration ';'     ;; 'localparam'
;  | {attribute_instance} parameter_override                  ;; 'defparam'
;  | {attribute_instance} continuous_assign                   ;; 'assign'
;  | {attribute_instance} gate_instantiation                  ;; [see below]
;  | {attribute_instance} udp_instantiation                   ;; identifier
;  | {attribute_instance} module_instantiation                ;; identifier
;  | {attribute_instance} initial_construct                   ;; 'initial'
;  | {attribute_instance} always_construct                    ;; 'always'
;  | {attribute_instance} loop_generate_construct             ;; 'for'
;  | {attribute_instance} conditional_generate_construct      ;; 'if' or 'case'
;
; Net declarations begin with a net_type or a trireg.
;
; Gate instantiations begin with one of the many *vl-gate-type-keywords*.

(defconst *vl-netdecltypes-kwds*
  (strip-cars *vl-netdecltypes-kwd-alist*))

(defparser vl-parse-module-or-generate-item (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (cond ((not (consp tokens))
         (vl-parse-error "Unexpected EOF."))
        ((member-eq (vl-token->type (car tokens)) *vl-netdecltypes-kwds*)
         (seqw tokens warnings
               ((assigns . decls) := (vl-parse-net-declaration atts))
               (return (append assigns decls))))
        ((member-eq (vl-token->type (car tokens)) *vl-gate-type-keywords*)
         (vl-parse-gate-instantiation atts tokens))
        (t
         (case (vl-token->type (car tokens))
           (:vl-kwd-reg        (vl-parse-reg-declaration atts))
           (:vl-kwd-integer    (vl-parse-integer-declaration atts))
           (:vl-kwd-real       (vl-parse-real-declaration atts))
           (:vl-kwd-time       (vl-parse-time-declaration atts))
           (:vl-kwd-realtime   (vl-parse-realtime-declaration atts))
           (:vl-kwd-event      (vl-parse-event-declaration atts))
           (:vl-kwd-genvar     (vl-parse-genvar-declaration atts))
           (:vl-kwd-task       (vl-parse-task-declaration atts))
           (:vl-kwd-function   (vl-parse-function-declaration atts))
           (:vl-kwd-localparam
            (seqw tokens warnings
                  ;; Note: non-local parameters not allowed
                  (ret := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-localparam)))
                  (:= (vl-match-token :vl-semi))
                  (return ret)))
           (:vl-kwd-defparam   (vl-parse-parameter-override atts))
           (:vl-kwd-assign     (vl-parse-continuous-assign atts))
           (:vl-idtoken        (vl-parse-udp-or-module-instantiation atts))
           (:vl-kwd-initial    (vl-parse-initial-construct atts))
           (:vl-kwd-always     (vl-parse-always-construct atts))
           (:vl-kwd-for        (vl-parse-loop-generate-construct atts))
           ((:vl-kwd-if :vl-kwd-case) (vl-parse-conditional-generate-construct atts))
           (t
            (vl-parse-error "Invalid module or generate item."))))))

(defparser vl-parse-non-port-module-item (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  :hint-chicken-switch t
  (cond ((vl-is-token? :vl-kwd-generate)
         (if atts
             (vl-parse-error "'generate' is not allowed to have attributes.")
           (vl-parse-generate-region)))
        ((vl-is-token? :vl-kwd-specify)
         (if atts
             (vl-parse-error "'specify' is not allowed to have attributes.")
           (vl-parse-specify-block)))
        ((vl-is-token? :vl-kwd-parameter)
         (seqw tokens warnings
               ;; localparams are handled in parse-module-or-generate-item
               (ret := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-parameter)))
               (:= (vl-match-token :vl-semi))
               (return ret)))
        ((vl-is-token? :vl-kwd-specparam)
         (vl-parse-specparam-declaration atts))
        (t
         (vl-parse-module-or-generate-item atts))))

(defparser vl-parse-module-item (tokens warnings)
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (when (vl-is-some-token? *vl-directions-kwds*)
          ((portdecls . netdecls) := (vl-parse-port-declaration-noatts atts))
          (:= (vl-match-token :vl-semi))
          ;; Should be fewer netdecls so this is the better order for the append.
          (return (append netdecls portdecls)))
        (ret := (vl-parse-non-port-module-item atts))
        (return ret)))




; module_parameter_port_list ::= '#' '(' parameter_declaration { ',' parameter_declaration } ')'

(defparser vl-parse-module-parameter-port-list-aux (tokens warnings)
  ;; parameter_declaration { ',' parameter_declaration }
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        ;; No attributes, no localparams allowed.
        (first := (vl-parse-param-or-localparam-declaration nil nil))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-module-parameter-port-list-aux)))
        (return (append first rest))))

(defparser vl-parse-module-parameter-port-list (tokens warnings)
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-pound))
        (:= (vl-match-token :vl-lparen))
        (params := (vl-parse-module-parameter-port-list-aux))
        (:= (vl-match-token :vl-rparen))
        (return params)))



;                                    MODULES
;
; module_declaration ::=
;
;   // I call this "Variant 1"
;
;    {attribute_instance} module_keyword identifier [module_parameter_port_list]
;        list_of_ports ';' {module_item}
;        'endmodule'
;
;
;   // I call this "Variant 2"
;
;  | {attribute_instance} module_keyword identifier [module_parameter_port_list]
;        [list_of_port_declarations] ';' {non_port_module_item}
;        'endmodule'
;
; module_keyword ::= 'module' | 'macromodule'
;

(defparser vl-parse-module-items-until-endmodule (tokens warnings)
  ;; Look for module items until :vl-kwd-endmodule is encountered.
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endmodule)
          (return nil))
        (first := (vl-parse-module-item))
        (rest := (vl-parse-module-items-until-endmodule))
        (return (append first rest))))

(defparser vl-parse-non-port-module-items-until-endmodule (tokens warnings)
  ;; Look for non-port module items until :vl-kwd-endmodule is encountered.
  :result (vl-moduleitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endmodule)
          (return nil))
        (atts := (vl-parse-0+-attribute-instances))
        (first := (vl-parse-non-port-module-item atts))
        (rest := (vl-parse-non-port-module-items-until-endmodule))
        (return (append first rest))))


(defparser vl-parse-module-declaration-variant-1 (atts module_keyword id tokens warnings)
  :guard (and (vl-atts-p atts)
              (vl-token-p module_keyword)
              (vl-idtoken-p id)
              ;; Ugly, adds warninglist-p hyps to our theorems
              (vl-warninglist-p warnings))
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong

; We try to match Variant 1:
;
;    {attribute_instance} module_keyword identifier [module_parameter_port_list]
;        list_of_ports ';' {module_item}
;        'endmodule'
;
; But we assume that
;
;   (1) the attributes, "module" or "macromodule", and the name of this module
;       have already been read, and
;
;   (2) the warnings we're given are initially NIL, so all warnings we come up
;       with until the end of the module 'belong' to this module.

  (seqw tokens warnings
        (when (vl-is-token? :vl-pound)
          (params := (vl-parse-module-parameter-port-list)))
        (when (vl-is-token? :vl-lparen)
          (ports := (vl-parse-list-of-ports)))
        (:= (vl-match-token :vl-semi))
        (items := (vl-parse-module-items-until-endmodule))
        (endkwd := (vl-match-token :vl-kwd-endmodule))
        (return (vl-make-module-by-items (vl-idtoken->name id)
                                         params ports items atts
                                         (vl-token->loc module_keyword)
                                         (vl-token->loc endkwd)
                                         warnings))))


(defund vl-ports-from-portdecls (x)
  (declare (xargs :guard (vl-portdecllist-p x)))
  (if (atom x)
      nil
    (b* ((name (vl-portdecl->name (car x)))
         (loc  (vl-portdecl->loc (car x)))
         (guts (make-vl-id :name name))
         (expr (make-vl-atom :guts guts)))
      (cons (make-vl-port :name name :expr expr :loc loc)
            (vl-ports-from-portdecls (cdr x))))))

(defthm vl-portlist-p-of-vl-ports-from-portdecls
  (implies (vl-portdecllist-p x)
           (vl-portlist-p (vl-ports-from-portdecls x)))
  :hints(("Goal" :in-theory (enable vl-ports-from-portdecls))))


(defparser vl-parse-module-declaration-variant-2 (atts module_keyword id tokens warnings)
  :guard (and (vl-atts-p atts)
              (vl-token-p module_keyword)
              (vl-idtoken-p id)
              (vl-warninglist-p warnings))
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong

; This is for Variant 2.
;
;  | {attribute_instance} module_keyword identifier [module_parameter_port_list]
;        [list_of_port_declarations] ';' {non_port_module_item}
;        'endmodule'

  (seqw tokens warnings
        (when (vl-is-token? :vl-pound)
          (params := (vl-parse-module-parameter-port-list)))
        (when (vl-is-token? :vl-lparen)
          ((portdecls . netdecls) := (vl-parse-list-of-port-declarations)))
        (:= (vl-match-token :vl-semi))
        (items := (vl-parse-non-port-module-items-until-endmodule))
        (endkwd := (vl-match-token :vl-kwd-endmodule))
        (return (vl-make-module-by-items (vl-idtoken->name id)
                                         params
                                         (vl-ports-from-portdecls portdecls)
                                         (append netdecls portdecls items)
                                         atts
                                         (vl-token->loc module_keyword)
                                         (vl-token->loc endkwd)
                                         warnings))))



(defparser vl-skip-through-endmodule (tokens warnings)
  :result (vl-token-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong

; This is a special function which is used to provide more fault-tolerance in
; module parsing.  We just advance the token stream until :vl-kwd-endmodule is
; encountered, and return the token itself.

  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endmodule)
          (end := (vl-match-token :vl-kwd-endmodule))
          (return end))
        (:s= (vl-match-any))
        (end := (vl-skip-through-endmodule))
        (return end)))


(defund vl-make-module-with-parse-error (name minloc maxloc err1 err2 tokens1 tokens2)
  (declare (xargs :guard (and (stringp name)
                              (vl-location-p minloc)
                              (vl-location-p maxloc)
                              (vl-tokenlist-p tokens1)
                              (vl-tokenlist-p tokens2)
                              )))
  (b* (;; We expect that ERR1 and ERR2 are objects suitable for cw-obj, i.e.,
       ;; each should be a cons of a string onto some arguments.  But if this
       ;; is not the case, we handle it here by just making a generic error.
       ((mv msg1 args1)
        (if (and (consp err1)
                 (stringp (car err1)))
            (mv (car err1) (list-fix (cdr err1)))
          (mv "Generic error message for modules with parse errors. ~% ~
               Details: ~x0.~%" (list err1))))

       ((mv msg2 args2)
        (if (and (consp err2)
                 (stringp (car err2)))
            (mv (car err2) (list-fix (cdr err2)))
          (mv "Generic error message for modules with parse errors. ~% ~
               Details: ~x0.~%" (list err2))))

       (warn1 (make-vl-warning :type :vl-parse-error
                               :msg msg1
                               :args args1
                               :fatalp t
                               :fn 'vl-make-module-with-parse-error))
       (warn2 (make-vl-warning :type :vl-parse-error
                               :msg msg2
                               :args args2
                               :fatalp t
                               :fn 'vl-make-module-with-parse-error))

       ;; We also generate a second error message to show the remaining part of
       ;; the token stream in each case:
       (warn3 (make-vl-warning :type :vl-parse-error
                               :msg "[[ Remaining ]]: ~s0 ~s1.~%"
                               :args (list (vl-tokenlist->string-with-spaces
                                            (take (min 4 (len tokens1))
                                                  (redundant-list-fix tokens1)))
                                           (if (> (len tokens1) 4) "..." ""))
                               :fatalp t
                               :fn 'vl-make-module-with-parse-error))
       (warn4 (make-vl-warning :type :vl-parse-error
                               :msg "[[ Remaining ]]: ~s0 ~s1.~%"
                               :args (list (vl-tokenlist->string-with-spaces
                                            (take (min 4 (len tokens2))
                                                  (redundant-list-fix tokens2)))
                                           (if (> (len tokens2) 4) "..." ""))
                               :fatalp t
                               :fn 'vl-make-module-with-parse-error)))

    (make-vl-module :name name
                    :origname name
                    :minloc minloc
                    :maxloc maxloc
                    :warnings (list warn1 warn2 warn3 warn4))))

(defthm vl-module-p-of-vl-make-module-with-parse-error
  (implies (and (force (stringp name))
                (force (vl-location-p minloc))
                (force (vl-location-p maxloc))
                (force (vl-tokenlist-p tokens1))
                (force (vl-tokenlist-p tokens2)))
           (vl-module-p (vl-make-module-with-parse-error name minloc maxloc
                                                         err1 err2
                                                         tokens1 tokens2)))
  :hints(("Goal" :in-theory (enable vl-make-module-with-parse-error))))



(defparser vl-parse-module-declaration (atts tokens warnings)
  :guard (and (vl-atts-p atts)
              ;; BOZO ugly.  This looks redundant, but it adds the warninglistp thing
              ;; to our theorems.
              (vl-warninglist-p warnings))
  :result (vl-module-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-some-token '(:vl-kwd-module :vl-kwd-macromodule)))
        (id  := (vl-match-token :vl-idtoken))
        (return-raw
         (b* (((mv err1 mod v1-tokens &)
               ;; A weird twist is that we want to associate all warnings
               ;; encountered during the parsing of a module with that module
               ;; as it is created, and NOT return them in the global list of
               ;; warnings.  Because of this, we use a fresh warnings
               ;; accumulator here.
               (vl-parse-module-declaration-variant-1 atts kwd id tokens nil))

              ((unless err1)
               ;; Successfully parsed the module using variant 1.  We return
               ;; the results from variant-1, except that we've already
               ;; trapped the v1-warnings and associated them with mod, so we
               ;; can just restore the previously encountered warnings.
               (mv err1 mod v1-tokens warnings))

              ((mv err2 mod v2-tokens &)
               (vl-parse-module-declaration-variant-2 atts kwd id tokens nil))
              ((unless err2)
               (mv err2 mod v2-tokens warnings)))

           ;; If we get this far, we saw "module foo" but were not able to
           ;; parse the rest of this module definiton.  We attempt to be
           ;; somewhat fault-tolerant by advancing all the way to endtoken.
           ;; Note that we backtrack all the way to the start of the module.
           (seqw tokens warnings
                 (endkwd := (vl-skip-through-endmodule tokens))
                 (return
                  (vl-make-module-with-parse-error (vl-idtoken->name id)
                                                   (vl-token->loc kwd)
                                                   (vl-token->loc endkwd)
                                                   err1
                                                   err2
                                                   v1-tokens
                                                   v2-tokens)))))))



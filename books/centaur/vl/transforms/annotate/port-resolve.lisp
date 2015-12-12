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
(include-book "../../mlib/scopestack")
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/filter")
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (Tau-system))))

(defxdoc port-resolve
  :parents (annotate)
  :short "Tricky post-parsing code to get all the ports straightened out."
  :long "<p>BOZO document me.</p>")

(local (xdoc::set-default-parents port-resolve))


;; BOZO temporary shim until we figure out how case/kind macros should work for
;; transparent sums.
(defmacro vl-port-kind (x) `(tag (vl-port-fix ,x)))

(defmacro vl-port-case (x &key vl-interfaceport vl-regularport)
  `(if (eq (vl-port-kind ,x) :vl-interfaceport)
       ,vl-interfaceport
     ,vl-regularport))


;; ===================== Fixing up ANSI Ports ====================================


(define vl-interface/type-warn-about-unexpected-lookup ((name stringp)
                                                        (lookup)
                                                        (expected-tag symbolp))
  :returns (warnings vl-warninglist-p)
  (b* ((warnings nil))
    (if (and (consp lookup)
             (not (eq (tag lookup) (mbe :logic (acl2::symbol-fix expected-tag)
                                        :exec expected-tag))))
        (warn :type :vl-bad-type-or-interface
              :msg "Identifier ~a0 looks like it should be a type or ~
                  interface name, but we found ~a1 instead."
              :args (list (string-fix name) lookup))
      (ok))))

(define vl-name-is-interface-or-type ((x stringp)
                                      (ss vl-scopestack-p))
  :short "Looks up x in the scopestack to see if it looks like an interface or
          type name.  Warns if the result was ambiguous."
  :returns (mv (warnings vl-warninglist-p)
               (looks-like-interface)
               (looks-like-type))
  (b* ((x (string-fix x))
       (type-lookup (vl-scopestack-find-item x ss))
       (iface-lookup (vl-scopestack-find-definition x ss))
       (warnings nil)
       ((wmv warnings)
        (vl-interface/type-warn-about-unexpected-lookup x type-lookup :vl-typedef))
       ((wmv warnings)
        (vl-interface/type-warn-about-unexpected-lookup x iface-lookup :vl-interface))
       ((when (and type-lookup (eq (tag type-lookup) :vl-typedef)))
        (if (and iface-lookup (eq (tag iface-lookup) :vl-interface))
            (mv (warn :type :vl-ambiguous-type-or-interface
                      :msg "Identifier ~a0 refers to an interface but also to ~
                            a typedef, ~a1."
                      :args (list x type-lookup))
                t t)
          (mv warnings nil t)))
       ((when (and iface-lookup (eq (tag iface-lookup) :vl-interface)))
        (mv warnings t nil)))
    (mv (warn :type :vl-ambiguous-type-or-interface
              :msg "Didn't find either an interface or typedef for identifier ~
                    ~a0."
              :args (list x))
        nil nil)))





(define vl-nettype-for-parsed-ansi-port
  :short "Determine the net type to use for a port."
  ((dir  vl-direction-p)
   (x    vl-ansi-portdecl-p))
  :returns (nettype vl-maybe-nettypename-p)
  :long "<p>From SystemVerilog-2012 23.2.2.3, \"the term \"port kind\" is used
to mean any of the net type keywords, or the keyword var, which are used to
explicitly declare a port of one of these kinds...\"</p>

<p>For ports in an ANSI port list, the rules for determining the port kind
appear to be the same for the first port and for subsequent ports.  (Pages 667
and 668).</p>

<p>The rules depend on the direction of the port.</p>

<ul>

<li>\"For input and inout ports, the port shall default to a net of the default
net type.\"  In VL the default nettype is always wire so this is easy.</li>

<li>\"For output ports, the default port kind depends on how the data type
is specified.
<ul>
<li>If the data type is omitted or declared with the implicit_data_type syntax, the
    port kind shall default to a net of the default net type.</li>

<li>If the data type is declared with the explicit datatype syntax, the port
    shall default to a variable.\"</li>
</ul></li>

</ul>"

  (b* (((vl-ansi-portdecl x)))
    (cond (x.nettype x.nettype)  ;; Explicitly provided net type; use it.
          (x.varp nil)          ;; Explicitly provided 'var' keyword, nettype is NIL.
          ((eq (vl-direction-fix dir) :vl-output)
           (if x.type
               ;; explicit data type so it's a variable (nettype nil)
               nil
             ;; no explicit declaration, use default net type, i.e., plain wire
             :vl-wire))
          (t
           ;; input/inout, use default net type, i.e., plain wire
           :vl-wire))))

(define vl-ansi-portdecl-regularport-type ((x vl-ansi-portdecl-p))
  :returns (type vl-datatype-p)
  (b* (((vl-ansi-portdecl x)))
    ;; 23.2.2.3: "If the data type is omitted, it shall default to
    ;; logic except for interconnect ports which have no data type."
    ;;
    ;; We don't implement interconnect ports yet so that's no problem.
    ;; Otherwise, if the data type is omitted, then we already made a
    ;; logic datatype when we parsed the header.
    (cond (x.typename
           (make-vl-usertype :name (vl-idscope x.typename)
                             :udims x.udims))
          (x.type
           (vl-datatype-update-udims x.udims x.type))
          (t (make-vl-coretype :name :vl-logic
                               :signedp (eq x.signedness :vl-signed)
                               :pdims x.pdims
                               :udims x.udims)))))


(define vl-ansi-portdecl-to-regularport-from-previous-regularport
  ((x vl-ansi-portdecl-p)
   (prev      vl-portdecl-p "Previous portdecl.")
   (prev-var  vl-vardecl-p  "Previous vardecl.")
   (warnings  vl-warninglist-p))
  :short "Assumes that x was just a plain variable, so it inherits all its info
          from the previous port."
  :returns (mv (warnings vl-warninglist-p)
               (port vl-regularport-p)
               (portdecl (and (vl-portdecllist-p portdecl)
                              (equal (len portdecl) 1)))
               (vardecl  (and (vl-vardecllist-p vardecl)
                              (equal (len vardecl) 1))))

  (b* (((vl-ansi-portdecl x) (vl-ansi-portdecl-fix x))
       ((vl-portdecl prev))
       ((vl-vardecl prev-var)))
       ;; 23.2.2.2: "If the direction, port kind, and data type are all
       ;; omitted, then they shall be inherited from the previous port."

    (mv (ok)
        (make-vl-regularport :name x.name
                             :expr (vl-idexpr x.name)
                             :loc x.loc)
        (list (make-vl-portdecl :name x.name
                                :dir prev.dir
                                :nettype prev.nettype
                                :type prev.type
                                :atts x.atts
                                :loc x.loc))
        (list (make-vl-vardecl :name x.name
                               :nettype prev.nettype
                               :type prev.type
                               :varp prev-var.varp
                               :atts x.atts
                               :loc x.loc)))))


(local (defthm len-of-collect-regular-ports-when-car
         (implies (and (equal (vl-port-kind (car ports)) :vl-regularport)
                       (consp ports))
                  (posp (len (vl-collect-regular-ports ports))))
         :hints(("Goal" :expand ((vl-collect-regular-ports ports))
                 :in-theory (enable vl-regularport-fix
                                    vl-port-fix
                                    ;tag
                                    )))
         :rule-classes :type-prescription))

(local (defthm vl-port-kind-of-vl-regularport
         (equal (vl-port-kind (vl-regularport name expr loc))
                :vl-regularport)))
         ;; :hints(("Goal" :in-theory (enable vl-regularport
         ;;                                   tag
         ;;                                   )))))


(local (in-theory (enable tag-reasoning)))

(define vl-ansi-portdecl-to-regularport
  ((x vl-ansi-portdecl-p)
   (ports-acc vl-portlist-p
              "Previous ports.  Empty implies this is the first.")
   (portdecls-acc vl-portdecllist-p
                  "Previous portdecls -- may be shorter than ports-acc.")
   (warnings vl-warninglist-p))
  :short "Assumes x was NOT just a plain identifier (or we are in the erroneous
          case where it was a plain identifier, but there was no previous port
          to base it on.)  Type and nettype info comes from x itself; only the
          direction may come from the previous port."
  :guard (equal (len portdecls-acc)
                (len (vl-collect-regular-ports ports-acc)))
  :returns (mv (warnings vl-warninglist-p)
               (port vl-regularport-p)
               (portdecl? (and (vl-portdecllist-p portdecl?)
                               (equal (len portdecl?)
                                      (vl-port-case port
                                        :vl-interfaceport 0
                                        :vl-regularport 1))))
               (vardecl?  (and (vl-vardecllist-p vardecl?)
                               (equal (len vardecl?)
                                      (vl-port-case port
                                        :vl-interfaceport 0
                                        :vl-regularport 1)))))
  (b* (((vl-ansi-portdecl x) (vl-ansi-portdecl-fix x))
       ;; 23.2.2.2: "If the direction, port kind, and data type are all
       ;; omitted, then they shall be inherited from the previous port."

       ;; 23.2.2.3.  For subsequent ports in the list, if the direction is
       ;; omitted then it shall be inherited from the previous port.
       ((mv dir warnings)
        (cond (x.dir (mv x.dir (ok)))
              ((atom ports-acc)
               ;; 23.2.2.3: "For the first port in the list, if the direction is
               ;; omitted, it shall default to inout."
               (mv :vl-inout nil))
              (t (b* ((port1 (car ports-acc)))
                   (vl-port-case port1
                     :vl-regularport (mv (vl-portdecl->dir (car portdecls-acc)) (ok))
                     :vl-interfaceport
                     (mv :vl-inout
                         (fatal :type :vl-bad-ports
                                :msg "~a0: can't infer direction for port ~a1 ~
                                      since it follows an interface port.  ~
                                      Please explicitly specify a direction ~
                                      (input, output, ...)"
                                :args (list x.loc x.name))))))))


       (nettype (vl-nettype-for-parsed-ansi-port dir x))
       (type (vl-ansi-portdecl-regularport-type x)))

    (mv (ok)
        (make-vl-regularport :name x.name
                             :expr (vl-idexpr x.name)
                             :loc x.loc)
        (list (make-vl-portdecl :name x.name
                                :dir dir
                                :nettype nettype
                                :type type
                                :atts x.atts
                                :loc x.loc))
        (list (make-vl-vardecl :name x.name
                               :nettype nettype
                               :type type
                               :varp x.varp
                               :atts x.atts
                               :loc x.loc)))))



(define vl-ansi-portdecl-to-interfaceport ((x vl-ansi-portdecl-p))
  :guard (vl-ansi-portdecl->typename x)
  :returns (port vl-interfaceport-p)
  (b* (((vl-ansi-portdecl x)))
    (make-vl-interfaceport :name x.name
                           :ifname x.typename
                           :modport x.modport
                           :udims x.udims
                           :loc x.loc)))

(define vl-ansi-portdecl-consistency-check ((x vl-ansi-portdecl-p))
  :returns (warnings vl-warninglist-p)
  (b* (((vl-ansi-portdecl x) (vl-ansi-portdecl-fix x))
       (warnings nil)
       ;; typename should imply no type, signedness, or pdims
       (warnings (if (and x.typename
                          (or x.type x.signedness x.pdims))
                     (warn :type :vl-ansi-portdecl-programming-error
                           :msg "~a0: If there is a typename there shouldn't ~
                                 be type, signedness, or pdims."
                           :args (list x))
                   warnings))
       ;; type should imply no signedness or pdims
       (warnings (if (and x.type
                          (or x.signedness x.pdims))
                     (warn :type :vl-ansi-portdecl-programming-error
                           :msg "~a0: If there is an explicit datatype there ~
                                 shouldn't be signedness or pdims."
                           :args (list x))
                   warnings))
       ;; modport should imply typename and not var-p, dir, or nettype
       (warnings (if (and x.modport (not x.typename))
                     (warn :type :vl-ansi-portdecl-programming-error
                           :msg "~a0: If there is a modport there should be a ~
                                 typename."
                           :args (list x))
                   warnings))
       (warnings (if (and x.modport (or x.varp x.dir x.nettype))
                     (warn :type :vl-ansi-portdecl-programming-error
                           :msg "~a0: If there is a modport there shouldn't ~
                                 be a direction or nettype or the var keyword."
                           :args (list x))
                   warnings)))
    warnings))


;; (local (defthm vl-port-p-when-vl-regularport-p-strong
;;          (implies (vl-regularport-p x)
;;                   (vl-port-p x))))

;; (local (defthm not-vl-interfaceport-p-when-regularport-p
;;          (implies (vl-regularport-p x)
;;                   (not (vl-interfaceport-p x)))
;;          :hints(("Goal" :in-theory (enable vl-interfaceport-p
;;                                            vl-regularport-p)))))


;; BOZO this is horrible
;; (local (defthm vl-port-kind-to-tag
;;          (implies (vl-port-p x)
;;                   (equal (vl-port-kind x) (tag x)))
;;          :hints(("Goal" :in-theory (enable vl-port-p vl-port-kind
;;                                            vl-interfaceport-p
;;                                            vl-regularport-p
;;                                            tag)))))

(local (defthm tag-when-vl-interfaceport-p-unrestricted
         (implies (vl-interfaceport-p x)
                  (equal (tag x) :vl-interfaceport))))

(local (defthm tag-when-vl-regularport-p-unrestricted
         (implies (vl-regularport-p x)
                  (equal (tag x) :vl-regularport))))




(define vl-ansi-portdecl-resolve
  ((x vl-ansi-portdecl-p)
   (ports-acc vl-portlist-p
              "Previous ports.  Empty implies this is the first.")
   (portdecls-acc vl-portdecllist-p
                  "Previous portdecls -- may be shorter than ports-acc.")
   (vardecls-acc  vl-vardecllist-p)
   (ss vl-scopestack-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :short "Turns an ANSI portdecl into a real port, (possible) portdecl,
and (possible) vardecl."
  :long "<p>This takes care of ambiguous interface ports in ANSI modules, and
also creates implicit variable declarations.  We assume these do not already
exist; if they do, we'll be creating new ones, but this should be checked by
make-implicit-wires.</p>

<p>This warns if there is an ambiguity in whether it's an interface or regular
port, but does not warn about all possible bad cases.  E.g., if it's known to
be a regular port, we don't look up the datatype to make sure it exists.</p>"

  :guard (and (equal (len portdecls-acc)
                     (len (vl-collect-regular-ports ports-acc)))
              (equal (len vardecls-acc)
                     (len (vl-collect-regular-ports ports-acc))))
  :returns (mv (warnings vl-warninglist-p)
               (port vl-port-p)
               (portdecl? (and (vl-portdecllist-p portdecl?)
                               (equal (len portdecl?)
                                      (vl-port-case port
                                        :vl-interfaceport 0
                                        :vl-regularport 1))))
               (vardecl?  (and (vl-vardecllist-p vardecl?)
                               (equal (len vardecl?)
                                      (vl-port-case port
                                        :vl-interfaceport 0
                                        :vl-regularport 1)))))

  (b* (((vl-ansi-portdecl x) (vl-ansi-portdecl-fix x))
       (warnings nil)
       ((when (and (not x.dir)
                   (not x.nettype)
                   (not x.varp)
                   (not x.type)
                   (not x.typename)
                   (not x.pdims)
                   (not x.signedness)))
        (b* (((when (atom ports-acc))
              ;; This shouldn't happen because it indicates we should have
              ;; parsed a non-ANSI portlist.
              (b* ((warnings
                    (warn :type :vl-ansi-port-programming-error
                          :msg "~a0: When the first port in the list has no ~
                            direction, nettype, var keyword, datatype, or ~
                            dimensions, or signedness, then it should have ~
                            been parsed as a non-ANSI portlist."
                          :args (list x))))
                (vl-ansi-portdecl-to-regularport
                 x ports-acc portdecls-acc warnings)))
             (prev (vl-port-fix (car ports-acc))))
          (vl-port-case prev
            :vl-interfaceport
            (b* (((vl-interfaceport prev)))
              (mv warnings
                  (make-vl-interfaceport :name x.name
                                         :ifname prev.ifname
                                         :modport prev.modport
                                         :udims x.udims
                                         :loc x.loc)
                  nil nil))
            :vl-regularport
            (vl-ansi-portdecl-to-regularport-from-previous-regularport
             x (car portdecls-acc) (car vardecls-acc) warnings))))

       ;; We have something besides a plain identifier.
       ((unless (and x.typename
                     (not x.dir)
                     (not x.nettype)
                     (not x.varp)))
        ;; Unambiguously a regularport.
        (vl-ansi-portdecl-to-regularport x ports-acc portdecls-acc warnings))

       ((when x.modport)
        ;; Definitely an interfaceport.
        (mv warnings
            (vl-ansi-portdecl-to-interfaceport x)
            nil nil))

       ((wmv warnings is-interface is-type :ctx x)
        (vl-name-is-interface-or-type x.typename ss))

       (warnings (if (iff is-type is-interface)
                     (fatal :type :vl-ambiguous-port
                            :msg "~a0: Ambiguous whether this is an interface ~
                                  port because ~x1 is ~s2 an interface ~s3 a ~
                                  type name.  Making it ~s4 port."
                            :args
                            (if is-type
                                (list x x.typename "both" "and" "a regular")
                              (list x x.typename "neither" "nor" "an interface")))
                   warnings))

       ((when is-type)
        (vl-ansi-portdecl-to-regularport x ports-acc portdecls-acc warnings)))

    (mv warnings
        (vl-ansi-portdecl-to-interfaceport x)
        nil nil)))


(local (defthm vl-interfaceport-p-when-not-regularport-tag
         (implies (and (vl-port-p x)
                       (not (equal (tag x) :vl-regularport)))
                  (equal (tag x) :vl-interfaceport))
         :hints(("Goal" :in-theory (enable vl-port-p)))))


(define vl-resolve-ansi-portdecls
  ((x vl-ansi-portdecllist-p)
   (ports-acc vl-portlist-p)
   (portdecls-acc vl-portdecllist-p)
   (vardecls-acc vl-vardecllist-p)
   (ss vl-scopestack-p))
  :guard (and (equal (len portdecls-acc)
                     (len (vl-collect-regular-ports ports-acc)))
              (equal (len vardecls-acc)
                     (len (vl-collect-regular-ports ports-acc))))
  :returns (mv (warnings vl-warninglist-p)
               (ports vl-portlist-p)
               (portdecls vl-portdecllist-p)
               (vardecls vl-vardecllist-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (b* (((when (atom x))
        (mv nil
            (rev (vl-portlist-fix ports-acc))
            (rev (vl-portdecllist-fix portdecls-acc))
            (rev (vl-vardecllist-fix vardecls-acc))))
       ((mv warnings1 port1 portdecls1 vardecls1)
        (vl-ansi-portdecl-resolve (car x) ports-acc portdecls-acc vardecls-acc ss))
       ((mv warnings-rest ports portdecls vardecls)
        (vl-resolve-ansi-portdecls
         (cdr x)
         (cons port1 ports-acc)
         (append-without-guard portdecls1 portdecls-acc)
         (append-without-guard vardecls1 vardecls-acc)
         ss)))
    (mv (append-without-guard warnings1 warnings-rest)
        ports portdecls vardecls)))



(define vl-module-resolve-ansi-portdecls ((x vl-module-p)
                                          (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) (vl-module-fix x))
       ((unless x.parse-temps) x)
       ((vl-parse-temps x.temps) x.parse-temps)
       ((unless x.temps.ansi-p) x)
       ((mv warnings ports portdecls vardecls)
        (vl-resolve-ansi-portdecls x.temps.ansi-ports
                                   nil nil nil (vl-scopestack-push x ss))))
    (change-vl-module x
                      :warnings (append-without-guard warnings x.warnings)
                      :ports ports
                      :portdecls portdecls
                      :vardecls (append-without-guard vardecls x.vardecls)
                      :parse-temps (change-vl-parse-temps
                                    x.temps
                                    :loaditems
                                    (append-without-guard
                                     (vl-modelementlist->genelements portdecls)
                                     (vl-modelementlist->genelements vardecls)
                                     x.temps.loaditems)))))

(defprojection vl-modulelist-resolve-ansi-portdecls ((x vl-modulelist-p)
                                                     (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-resolve-ansi-portdecls x ss))

(define vl-interface-resolve-ansi-portdecls ((x vl-interface-p)
                                          (ss vl-scopestack-p))
  :returns (new-x vl-interface-p)
  (b* (((vl-interface x) (vl-interface-fix x))
       ((unless x.parse-temps) x)
       ((vl-parse-temps x.temps) x.parse-temps)
       ((unless x.temps.ansi-p) x)
       ((mv warnings ports portdecls vardecls)
        (vl-resolve-ansi-portdecls x.temps.ansi-ports
                                   nil nil nil (vl-scopestack-push x ss))))
    (change-vl-interface x
                      :warnings (append-without-guard warnings x.warnings)
                      :ports ports
                      :portdecls portdecls
                      :vardecls (append-without-guard vardecls x.vardecls)
                      :parse-temps (change-vl-parse-temps
                                    x.temps
                                    :loaditems
                                    (append-without-guard
                                     (vl-modelementlist->genelements portdecls)
                                     (vl-modelementlist->genelements vardecls)
                                     x.temps.loaditems)))))

(defprojection vl-interfacelist-resolve-ansi-portdecls ((x vl-interfacelist-p)
                                                     (ss vl-scopestack-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-resolve-ansi-portdecls x ss))



(define vl-design-resolve-ansi-portdecls ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) (vl-design-fix x))
       (ss (vl-scopestack-init x))
       (mods (vl-modulelist-resolve-ansi-portdecls x.mods ss))
       (ifs  (vl-interfacelist-resolve-ansi-portdecls x.interfaces ss)))
    (change-vl-design x :mods mods :interfaces ifs)))


;; ===================== Fixing up ANSI Ports ====================================

;; Several jobs here:

;; 1. Generate implicit vardecls for regular portdecls.

;; 2. Cross-propagate type information between var and portdecls.

;; 3. Recognize vardecls that are actually interface portdecls and replace them
;; with interface ports.

;; 4. Check ports to make sure they all have correct portdecls.


;; How to do this?

;; 1. This is done in make-implicit-wires.lisp, vl-make-port-implicit-wires.

;; 2. This is done in portdecl-sign.lisp.  It happens after shadowcheck, which
;; means we can reorder things, which is convenient for generating new vardecls
;; and not worrying about their order in the loaditems.

;; 3. Go through the loaditems and check vardecls that have simple usertypes
;; with only unpacked dimensions, no nettype, and no var keyword -- if the type
;; is an interface name and not a type name, then mark it as an interface port
;; and remove the vardecl.  Remove the interfaceports from the loaditems and
;; vardecls.  Go through the ports and replace the interfaceports.

;; 4. This is done in basicsanity



(define vl-vardecl-is-really-interfaceport ((x vl-vardecl-p)
                                            (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (ifport (iff (vl-interfaceport-p ifport) ifport)))
  (b* (((vl-vardecl x) (vl-vardecl-fix x))
       (warnings nil)
       ((when (or x.varp
                  x.nettype
                  (not (vl-datatype-case x.type :vl-usertype))
                  (not (vl-idscope-p (vl-usertype->name x.type)))
                  (consp (vl-datatype->pdims x.type))
                  ))
        ;; Not an interface port declaration, just syntactically.
        (mv warnings nil))
       (typename (vl-idscope->name (vl-usertype->name x.type)))
       ((wmv warnings is-interface is-type :ctx x)
        (vl-name-is-interface-or-type typename ss))

       (warnings (if (iff is-interface is-type)
                     (fatal :type :vl-ambiguous-declaration
                            :msg "~a0: Ambiguous whether this is a variable or ~
                                 interfaceport declaration, because ~a1 is ~
                                 ~s2 an interface ~s3 a type name."
                            :args (if is-interface
                                      (list x typename "both" "and")
                                    (list x typename "neither" "nor")))
                   warnings)))
    (mv warnings
        (and is-interface
             (make-vl-interfaceport :name x.name
                                    :ifname typename
                                    :modport nil
                                    :udims (vl-datatype->udims x.type)
                                    :loc x.loc)))))

(define vl-loaditems-remove-interfaceport-decls ((x vl-genelementlist-p)
                                                 (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-loaditems vl-genelementlist-p)
               (ifport-alist vl-interfaceport-alist-p))
  :prepwork ((local (in-theory (disable vl-interfaceport-p-when-not-regularport-tag
                                        vl-port-p-of-car-when-vl-portlist-p
                                        vl-genelement-p-by-tag-when-vl-scopeitem-p
                                        acl2::list-fix-when-len-zero
                                        true-listp append acl2::append-when-not-consp))))
  (b* (((when (atom x)) (mv nil nil nil))
       (warnings nil)
       ((wmv warnings rest rest-ifports)
        (vl-loaditems-remove-interfaceport-decls (cdr x) ss))
       (x1 (vl-genelement-fix (car x))))
    (vl-genelement-case x1
      :vl-genbase
      (b* (((unless (eq (tag x1.item) :vl-vardecl))
            (mv warnings (cons x1 rest) rest-ifports))
           ((wmv warnings ifport)
            (vl-vardecl-is-really-interfaceport x1.item ss))
           ((unless ifport)
            (mv warnings (cons x1 rest) rest-ifports)))
        (mv warnings rest
            (cons (cons (vl-vardecl->name x1.item) ifport)
                  rest-ifports)))
      :otherwise (mv warnings (cons x1 rest) rest-ifports))))


(define vl-ports-resolve-interfaces ((x vl-portlist-p)
                                     (ifport-alist vl-interfaceport-alist-p))
  :prepwork ((local (defthm vl-port-p-when-vl-interfaceport-p-strong
                      (implies (vl-interfaceport-p x) (vl-port-p x)))))
  :returns (new-x vl-portlist-p)
  (b* (((when (atom x)) nil)
       (x1 (vl-port-fix (car x)))
       (rest (vl-ports-resolve-interfaces (cdr x) ifport-alist))
       ((unless (eq (tag x1) :vl-regularport))
        (cons x1 rest))
       ((vl-regularport x1))
       ((unless (and x1.expr (vl-idexpr-p x1.expr)))
        ;; Complicated port expr -- not an interfaceport
        (cons x1 rest))
       (name (vl-idexpr->name x1.expr))
       (look (hons-get name (vl-interfaceport-alist-fix ifport-alist)))
       ((unless look) ;; not an interfaceport
        (cons x1 rest)))
    ;; Is an interfaceport -- use the one from the alist.
    (cons (cdr look) rest)))

(define vl-module-resolve-nonansi-interfaceports ((x vl-module-p)
                                                  (ss vl-scopestack-p))
  :prepwork ((local (defthm string-listp-alist-keys-of-interfaceport-alist
                      (implies (vl-interfaceport-alist-p x)
                               (string-listp (alist-keys x)))
                      :hints(("Goal" :in-theory (enable vl-interfaceport-alist-p
                                                        alist-keys))))))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) (vl-module-fix x))
       ((unless (and x.parse-temps
                     (not (vl-parse-temps->ansi-p x.parse-temps))))
        x)
       (ss (vl-scopestack-push x ss))
       (loaditems (vl-parse-temps->loaditems x.parse-temps))
       ((mv warnings new-loaditems ifport-alist)
        (vl-loaditems-remove-interfaceport-decls loaditems ss))
       (ifport-alist (make-fast-alist ifport-alist))
       (vardecls (with-local-nrev
                   (vl-fast-delete-vardecls (alist-keys ifport-alist) ifport-alist
                                            x.vardecls nrev)))
       (ports (vl-ports-resolve-interfaces x.ports ifport-alist)))
    (change-vl-module x
                      :vardecls vardecls
                      :ports ports
                      :parse-temps (change-vl-parse-temps x.parse-temps
                                                          :loaditems new-loaditems)
                      :warnings (append-without-guard warnings x.warnings))))

(defprojection vl-modulelist-resolve-nonansi-interfaceports ((x vl-modulelist-p)
                                                     (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-resolve-nonansi-interfaceports x ss))

(define vl-interface-resolve-nonansi-interfaceports ((x vl-interface-p)
                                                     (ss vl-scopestack-p))
  :prepwork ((local (defthm string-listp-alist-keys-of-interfaceport-alist
                      (implies (vl-interfaceport-alist-p x)
                               (string-listp (alist-keys x)))
                      :hints(("Goal" :in-theory (enable vl-interfaceport-alist-p
                                                        alist-keys))))))
  :returns (new-x vl-interface-p)
  (b* (((vl-interface x) (vl-interface-fix x))
       ((unless (and x.parse-temps
                     (not (vl-parse-temps->ansi-p x.parse-temps))))
        x)
       (ss (vl-scopestack-push x ss))
       (loaditems (vl-parse-temps->loaditems x.parse-temps))
       ((mv warnings new-loaditems ifport-alist)
        (vl-loaditems-remove-interfaceport-decls loaditems ss))
       (ifport-alist (make-fast-alist ifport-alist))
       (vardecls (with-local-nrev
                   (vl-fast-delete-vardecls (alist-keys ifport-alist) ifport-alist
                                            x.vardecls nrev)))
       (ports (vl-ports-resolve-interfaces x.ports ifport-alist)))
    (change-vl-interface x
                         :vardecls vardecls
                         :ports ports
                         :parse-temps (change-vl-parse-temps x.parse-temps
                                                             :loaditems new-loaditems)
                         :warnings (append-without-guard warnings x.warnings))))

(defprojection vl-interfacelist-resolve-nonansi-interfaceports ((x vl-interfacelist-p)
                                                     (ss vl-scopestack-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-resolve-nonansi-interfaceports x ss))

(define vl-design-resolve-nonansi-interfaceports ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) (vl-design-fix x))
       (ss (vl-scopestack-init x))
       (mods (vl-modulelist-resolve-nonansi-interfaceports x.mods ss))
       (ifs  (vl-interfacelist-resolve-nonansi-interfaceports x.interfaces ss)))
    (change-vl-design x :mods mods :interfaces ifs)))




(in-package "SVL")

(include-book "centaur/sv/svex/vars" :dir :system)

(include-book "centaur/fty/top" :dir :system)

(include-book "projects/apply/top" :dir :system)

(defmacro svl-name (module)
  `(nth 0 ,module))

(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/substrp" :dir :system)
(include-book "tools")
(include-book "macros")

(encapsulate
  nil
  (defun wire-p (wire)
    (declare (xargs :guard t))
    (case-match wire
      ((wire-name size . start)
       (and (or (stringp wire-name)
                (symbolp wire-name))
            (not (booleanp wire-name))
            (natp size)
            (natp start)))
      ((wire-name)
       (and (or (stringp wire-name)
                (symbolp wire-name))
            (not (booleanp wire-name))))
      (& nil)))

  (defun wire-fix (wire)
    (declare (xargs :guard t))
    (if (wire-p wire)
        wire
      `("" 1 . 0)))

  (defthm wire-p-wire-fix-x
    (wire-p (wire-fix x)))

  (defun wire-list-p (wires)
    (declare (xargs :guard t))
    (if (atom wires)
        (eq wires nil)
      (and (wire-p (car wires))
           (wire-list-p (cdr wires)))))

  (defun wire-list-fix (wires)
    (declare (xargs :guard t))
    (if (atom wires)
        nil
      (cons (wire-fix (car wires))
            (wire-list-fix (cdr wires)))))

  (defthm WIRE-LIST-P-WIRE-LIST-FIX-x
    (WIRE-LIST-P (WIRE-LIST-FIX ACL2::X))
    :hints (("Goal"
             :in-theory (e/d (WIRE-LIST-P
                              WIRE-LIST-FIX)
                             (wire-p
                              wire-fix)))))

  (fty::deffixtype wire-list
                   :pred  wire-list-p
                   :fix   wire-list-fix
                   :equiv equal)

  (define module-occ-wire-p (wire)
    :enabled t
    (and (consp wire)
         (stringp (car wire))
         (wire-p (cdr wire))))

  (define module-occ-wire-fix (wire)
    :enabled t
    (if (module-occ-wire-p wire)
        wire
      `("" . ("" 1 . 0))))

  (fty::deffixtype module-occ-wire
                   :pred  module-occ-wire-p
                   :fix   module-occ-wire-fix
                   :equiv equal)

  (defun module-occ-wire-list-p (wires)
    (declare (xargs :guard t))
    (if (atom wires)
        (eq wires nil)
      (and (module-occ-wire-p (car wires))
           (module-occ-wire-list-p (cdr wires)))))

  (defun module-occ-wire-list-fix (wires)
    (declare (xargs :guard t))
    (if (atom wires)
        nil
      (cons (module-occ-wire-fix (car wires))
            (module-occ-wire-list-fix (cdr wires)))))

  (fty::deffixtype module-occ-wire-list
                   :pred  module-occ-wire-list-p
                   :fix   module-occ-wire-list-fix
                   :equiv equal)

  (defmacro wire-name (wire)
    `(car ,wire))

  (defmacro wire-size (wire)
    `(cadr ,wire))

  (defmacro wire-start (wire)
    `(cddr ,wire)))

(encapsulate
  nil

  (define occ-name-p (x)
    (or (and (symbolp x)
             (not (booleanp x)))
        (stringp x))
    :returns (res booleanp))

  (define occ-name-fix (x)
    (if (occ-name-p x)
        x
      ""))

  ;(defprod 
  
  (defthm occ-name-p-occ-name-FIX-X
    (occ-name-p (occ-name-fix ACL2::X))
    :hints (("Goal"
             :in-theory (e/d (occ-name-p
                              occ-name-fix) ()))))

  (defthm occ-name-P-occ-name-FIX-X-2
    (IMPLIES (occ-name-p ACL2::X)
             (EQUAL (occ-name-fix ACL2::X)
                    ACL2::X))
    :hints (("Goal"
             :in-theory (e/d (occ-name-p
                              occ-name-fix) ()))))

  
  (fty::deffixtype occ-name
                   :pred  occ-name-p
                   :fix   occ-name-fix
                   :equiv occ-name-equiv
                   :define t
                   :forward t)

  (fty::deflist occ-name-list
                :elt-type occ-name)

  (fty::defalist occ-name-alist
                 :val-type occ-name-list
                 :key-type occ-name))

(fty::deftagsum
 occ
 (:assign ((inputs wire-list)
           (delayed-inputs occ-name-list)
           (outputs wire-list)
           (svex sv::svex-p)))
 (:module ((inputs module-occ-wire-list)
           (outputs module-occ-wire-list)
           (name stringp))))

(fty::defalist occ-alist
               :key-type occ-name
               :val-type occ)

#|(fty::defprod
 delayed-inputs
 ((wire-names occ-name-list)
  (modules))
 :layout :list)||#

(fty::defprod
 svl-module
 ((rank natp :default '0)
  (inputs string-listp)
  (delayed-inputs occ-name-list)
  (outputs string-listp)
  (wires wire-list-p)
  (occs occ-alist)
  (listeners occ-name-alist))
 :layout :alist)

(fty::defalist svl-module-alist
               :val-type svl-module
               :key-type stringp)

(defmacro svl-ins (module)
  `(svl-module->inputs ,module))

(defmacro svl-outs (module)
  `(svl-module->outputs ,module))

(defmacro svl-wires (module)
  `(svl-module->wires ,module))

(defmacro svl-occs (module)
  `(svl-module->occs ,module))

(defmacro svl-listeners (module)
  `(svl-module->listeners ,module))

(defmacro svl-delayed-ins (module)
  `(svl-module->delayed-inputs ,module))

(progn

  (defun vl-insouts-get-range (vl-logic)
    (b* (((unless (or (equal (car vl-logic)
                             ':VL-LOGIC)
                      (equal (car vl-logic)
                             'VL::PDIMS)))
          (progn$ (hard-error 'vl-smodule-get-range
                              "Unknown data type ~%"
                              nil)
                  (mv t nil)))
         (range (assoc-equal ':VL-RANGE (cdr vl-logic)))
         ((unless range)
          (mv t (cons '? '?)))
         (endp (cdadr (cadadr range)))
         (startp (cdadr (cadddr range))))

      (mv nil (cons (- (1+ (abs (- endp startp)))
                       0;(min endp startp)
                       )
                    0))))

  (defun vl-insouts-getwire (name wires)
    (if (atom wires)
        nil
      (if (equal name (caaar wires))
          (caar wires)
        (vl-insouts-getwire name (cdr wires)))))

  (defun vl-smodule-to-insouts (smodule )
    (if (atom smodule)
        (mv nil nil)
      (b* ((c (car smodule))
           (type (car c))
           ((mv inrest outrest)
            (vl-smodule-to-insouts (cdr smodule) ))
           ((when (not (equal type ':VL-PORTDECL)))
            (mv inrest outrest))
           (porttype (cddr (cadr c)))
           (portname (caadr c))
           (& (cw "porttype ~p0 ~p1 ~%" porttype portname))
           ((when (and (not (equal porttype ':VL-INPUT))
                       (not (equal porttype ':VL-OUTPUT))))
            (mv (hard-error "Unknown porttype. we only support input and output ~
    port types ~%" nil nil) nil))
           #|((mv & range) (vl-insouts-get-range (cadar (caddr c))))||#
           #|(wire (vl-insouts-getwire portname wires))||#
           (ins (if (equal porttype ':VL-INPUT)
                    (cons portname inrest)
                  inrest))
           (outs (if (equal porttype ':VL-OUTPUT)
                     (cons portname outrest)
                   outrest)))
        (mv ins outs))))

  (defun vl-ansi-ports-to-insouts (ports  most-recent-type )
    ;; For modules whose port types are declared right in the port list are
    ;; scanned here.
    (if (atom ports)
        (mv nil nil)
      (b* ((port (car ports))
           ((unless (equal (car port) ':VL-ANSI-PORTDECL))
            (progn$ (HARD-ERROR 'vl-ansi-ports-to-insouts
                                "Unexpected happened!!~%"
                                NIL)
                    (mv nil nil)))
           (port (cdr port))
           (portname (cdr (assoc-equal 'vl::NAME port)))
           (porttype (cdr (assoc-equal 'vl::dir port)))
           (porttype (if porttype porttype
                       most-recent-type))
           ((unless (or (equal porttype ':VL-INPUT)
                        (equal porttype ':VL-OUTPUT)))
            (progn$
             (hard-error 'vl-ansi-ports-to-insouts
                         "Unknown port type! ~%" nil)
             (mv nil nil)))
           ((mv rest-ins rest-outs)
            (vl-ansi-ports-to-insouts (cdr ports)  porttype)))
        (mv (if (equal porttype ':VL-INPUT)
                (cons portname rest-ins)
              rest-ins)
            (if (equal porttype ':VL-OUTPUT)
                (cons portname rest-outs)
              rest-outs)))))

  (defun vl-module-to-insouts (vl-module )
    (and
     (consp vl-module)
     (equal (car vl-module) ':VL-MODULE)
     (consp (cadr vl-module))
     (consp (caadr vl-module))
     (consp (caaadr vl-module))
     (b* ((smodule (caadr vl-module))
          (module-name (caaar smodule))
          ((mv ins outs)
           (vl-smodule-to-insouts (caadr smodule) ))
          ((mv ins2 outs2)
           (vl-ansi-ports-to-insouts
            (cdr (assoc-equal 'vl::ANSI-PORTS
                              (cadddr (cdddr vl-module))))

            nil)))
       (list* module-name (append ins ins2) (append outs outs2)))))

  (defun vl-modules-to-insouts (vl-modules )
    (if (atom vl-modules)
        nil
      (cons
       (b* (#|(module-name (caaar (caadar vl-modules)))||#
            #|(sv-module (cdr (assoc-equal module-name sv-modules)))||#
            #|(wires (cdr (assoc-equal 'sv::wires sv-module)))||#)
         (vl-module-to-insouts (car vl-modules)))
       (vl-modules-to-insouts (cdr vl-modules) ))))

  (defun insouts-add-missing-modules-aux (sv-module-name insouts)
    (if (atom insouts)
        nil
      (b* ((cur (car insouts))
           (name (car cur))
           ((when (and (stringp sv-module-name)
                       (stringp name)
                       (str::strprefixp (concatenate 'string name "$") sv-module-name)))
            (list* sv-module-name (cadr cur) (cddr cur))))
        (insouts-add-missing-modules-aux sv-module-name (cdr insouts)))))

  (defun insouts-add-missing-modules (insouts sv-modules)
    ;; some modules created with parameters for example width for input signals
    ;; does not show up in the original insouts lists. It is because sv-design
    ;; appends the parameter to the module's name whereas vl design does
    ;; not. SV design does this appending with $ sign so we search the existing
    ;; insouts list to find the origin of that missing module.
    (declare (ignorable sv-modules))
    (if (atom sv-modules)
        insouts
      (b* ((cur-sv-module (car sv-modules))
           (name (car cur-sv-module))
           ((when (assoc-equal name insouts))
            (insouts-add-missing-modules insouts (cdr sv-modules)))
           (new-insout (insouts-add-missing-modules-aux name insouts)))
        (if new-insout
            (insouts-add-missing-modules (cons new-insout insouts)
                                         (cdr sv-modules))
          (insouts-add-missing-modules insouts
                                       (cdr sv-modules))))))

  (defun vl-design-to-insouts (vl-design sv-design)
    (and (consp vl-design)
         (equal (car vl-design) ':VL-DESIGN)
         (consp (cadr vl-design))
         (consp (cadr vl-design))
         (consp (caadr vl-design))
         (consp (caaadr vl-design))
         (or (equal (car (caaadr vl-design)) "VL Syntax 2016-08-26")
             (hard-error "VL Syntax version is different exiting just in case ~
  ~%" nil nil))
         (b* ((insouts (vl-modules-to-insouts (cdr (caaadr vl-design))))
              (insouts (insouts-add-missing-modules insouts
                                                    (cdr (assoc-equal
                                                          'SV::MODALIST sv-design)))))
           insouts))))

(defun svl-assoc (key alist is-fast-alist)
  (declare (xargs :guard (alistp alist)))
  (if is-fast-alist
      (hons-get key alist)
    (assoc-equal key alist)))

(defun should-svl-module-be-fast-alist (sv-module)
  (> (+ (len (cdr (assoc-equal 'sv::insts sv-module)))
        (len (cdr (assoc-equal 'sv::assigns sv-module))))
     15))

(defun sv->svl-get-wire-sizes (sv-wires)
  (declare (xargs :mode :program))
  (if (atom sv-wires)
      nil
    (b* ((wire (car sv-wires))
         (wire-name (car wire))
         (wire-size (cadr wire))
         (- (If (< wire-size 0) (cw "wire: ~p0 ~%" wire) nil)))
      (hons-acons wire-name
                  (cons wire-size 0)
                  (sv->svl-get-wire-sizes (cdr sv-wires))))))

(defun sv->svl-get-insouts-for-occ-aux (o-signame signame o-start o-size start
                                                  size module-ins/outs)
  ;; o-* are from the alias-pair and they're sub-module's props.
  ;; signame/start/size are from alias-pair main-module's props.

  ;; module-ins/outs ins our outs lists for that sub-module's vl-insouts.

  ;; Goal: go through every module-ins/outs to see if they cover
  ;; o-signame with o-start and o-size.
  ;; if it does not cover it, then don't change module-ins/outs and go on.
  ;; if the cover is an exact match: remove from module-ins/outs, add pair to
  ;; resulting ins/outs list and exit.
  ;; if the cover is only partial and some part of module-ins/outs is left out;
  ;; crete the pair for the covered part and carve out the rest. Determine by
  ;; checking the common subset ---(NOT YET IMPLEMENTED)--- --It may never be necessary--
  (declare (xargs :mode :program))
  (if (atom module-ins/outs)
      (mv nil nil)
    (b* ((cur (car module-ins/outs))
         ((mv rest rest-m)
          (sv->svl-get-insouts-for-occ-aux o-signame signame
                                           o-start o-size
                                           start
                                           size
                                           (cdr module-ins/outs)))
         ((unless (equal o-signame cur))
          (mv rest (cons-with-hint (car module-ins/outs) rest-m module-ins/outs)))
         #|(m-size (cadr cur))||#
         #|(m-start (cddr cur))||#
         ((when (and #|(equal m-size o-size)||#
                 #|(equal m-start o-start)||#
                 (equal o-size size)))
          (mv (cons `(,o-signame . (,signame ,size . ,start))
                    rest)
              rest-m)))
      (progn$
       (cw "m-size = , o-size= ~p0, size=~p1, m-start= , o-start = ~p2
~%"
           #|m-size||# o-size size #|m-start||# o-start)
       (hard-error 'sv->svl-get-insouts-for-occ-aux
                   "Not yet implemented! ~%"
                   nil)
       (mv nil nil)))))

(defun sv->svl-get-insouts-for-occ-aux2 (occ-name module-ins/outs)
  (declare (xargs :mode :program))
  (if (atom module-ins/outs)
      nil
    (cons (list* ;;`(,(car module-ins/outs) ? . ?)
           ;; for the same reason in sv->svl-get-insouts-for-occ-aux
           (car module-ins/outs)
           (intern$ (str::cat occ-name "$" (car module-ins/outs))
                    *package-name*)
           1 ;; !!!!!!!!!!!!!!!!!!!! This is not right, instead I should
           ;; retrieve the size from the module itself
           0)
          (sv->svl-get-insouts-for-occ-aux2 occ-name (cdr module-ins/outs)))))

(defun sv->svl-get-insouts-for-occ (occ-name module-ins module-outs
                                             occ-alias-pairs)
  (declare (xargs :mode :program))
  ;; Example input:
  ;; occ-name = "ha10"
  ;; module-ins (("x" 1 . 0) ("y" 1 . 0))
  ;; module-outs (("sum" 1 . 0) ("c_out" 1 . 0))
  ;; occ-alias-pairs ((((:VAR ("ha10" . "sum") . 0)) ("result" . 1))
  ;;                  (((:VAR ("ha10" . "c_out") . 0)) "w10")
  ;;                  (((:VAR ("ha10" . "x") . 0)) ("r0" . 1))
  ;;                  (((:VAR ("ha10" . "y") . 0)) ("r1" . 1))
  ;;                  (((4 :VAR ("ha10" . "x") . 0)) (4 . "x")))
  ;; Goal: process and divide occ-alias-pairs into inputs and outputs lists
  ;; with respect to module-ins and module-outs.
  ;; If some signal in occ-alias-pairs is not covered with module-ins or
  ;; module-outs, ignore (or should throw and error?).
  ;; If some signal in module-ins or module-outs is not assigned, assign it to
  ;; itself.

  (if (atom occ-alias-pairs)
      (b* ((& "Do something here to add uncovered module-ins/outs"))
        (mv (sv->svl-get-insouts-for-occ-aux2 occ-name module-ins)
            (sv->svl-get-insouts-for-occ-aux2 occ-name module-outs)))
    (b* ((cur (car occ-alias-pairs))
         ((mv o-signame o-start o-size sig)
          (case-match cur
            ((((o-size ':VAR (& . o-signame) . o-start)) sig)
             (mv o-signame o-start o-size sig))
            ((((':VAR (& . o-signame) . o-start)) sig)
             (mv o-signame o-start 1 sig))
            ((((':VAR (& . o-signame))) sig)
             (mv o-signame 0 1 sig))
            (&
             (progn$
              (hard-error 'sv->svl-insts-get-inst-insouts-for-occ
                          "Unknown alias signature! ~%" nil)
              (mv "" 0 0 "")))))
         ((mv signame start size)
          (case-match sig
            ((size signame . start)
             (mv signame start size))
            ((a . b)
             (cond ((stringp a)
                    (mv a b 1))
                   (t
                    (mv b 0 a))))
            (&
             (mv sig 0 1))))
         ((mv ins module-ins)
          (sv->svl-get-insouts-for-occ-aux o-signame signame
                                           o-start o-size
                                           start size
                                           module-ins))
         ((mv outs module-outs)
          (sv->svl-get-insouts-for-occ-aux o-signame signame
                                           o-start o-size
                                           start size
                                           module-outs))
         ((mv rest-ins rest-outs)
          (sv->svl-get-insouts-for-occ occ-name module-ins module-outs
                                       (cdr occ-alias-pairs))))
      (mv (append ins rest-ins)
          (append outs rest-outs)))))

#|

(SV->SVL-GET-INSOUTS-FOR-OCC
 '(("x" 1 . 0) ("y" 1 . 0))
 '(("sum" 1 . 0) ("c_out" 1 . 0))
 '((((:VAR ("ha10" . "sum") . 0)) ("result" . 1))
   (((:VAR ("ha10" . "c_out") . 0)) "w10")
   (((:VAR ("ha10" . "x") . 0)) ("r0" . 1))
   (((:VAR ("ha10" . "y") . 0)) ("r1" . 1))
   (((4 :VAR ("ha10" . "k") . 0)) (4 . "k"))
   ))
||#

(defun sv->svl-aliaspairs-to-alist (aliaspairs)
  (declare (xargs :mode :program))
  ;; Goal is to take an aliaspairs list and convert it into an alist where
  ;; aliases for every occurance is seperated.
  ;; Returned value is a fast-alist
  ;; there will be a lot of shadowed pairs so running (fast-alist-clean *) on
  ;; the returned value can be necessary.
  (if (atom aliaspairs)
      nil
    (b* ((cur (car aliaspairs))
         (occ-name
          (case-match cur
            ((((& ':VAR (occ-name . &) . &)) &)
             occ-name)
            ((((':VAR (occ-name . &) . &)) &)
             occ-name)
            ((((':VAR (occ-name . &))) &)
             occ-name)
            (&
             (progn$
              (cw "WARNING! Unknown alias signature for ~p0 ~%" cur)
              #|(hard-error 'sv->svl-aliaspairs-to-alist
              "Unknown alias signature! ~%" nil)||#
              nil))))
         (rest (sv->svl-aliaspairs-to-alist (cdr aliaspairs)))
         ((unless occ-name) rest)
         (rest-e (hons-get occ-name rest)))
      (if rest-e
          (hons-acons occ-name
                      (cons cur (cdr rest-e))
                      rest)
        (hons-acons occ-name
                    (cons cur nil)
                    rest)))))

#|
(b* ((alist
      (sv->svl-aliaspairs-to-alist '((((4 :VAR ("booth" . "mr") . 0))
                        (4 . "mr"))
                       (((4 :VAR ("booth" . "md") . 0))
                        (4 . "md"))
                       (((4 :VAR ("booth" . "x") . 0))
                        (4 . "x"))
                       (((4 :VAR ("booth" . "z") . 0))
                        (4 . "z"))
                       (((4 :VAR ("pp" . "x") . 0)) (4 . "x"))
                       (((4 :VAR ("pp" . "z") . 0)) (4 . "z"))
                       (((8 :VAR ("pp" . "r0") . 0))
                        (8 . "r0"))
                       (((8 :VAR ("pp" . "r1") . 0))
                        (8 . "r1"))
                       (((8 :VAR ("pp" . "r2") . 0))
                        (8 . "r2"))
                       (((8 :VAR ("pp" . "r3") . 0))
                        (8 . "r3"))
                       (((4 :VAR ("pp" . "md") . 0))
                        (4 . "md"))
                       (((4 :VAR ("pp" . "mr") . 0))
                        (4 . "mr"))
                       (((8 :VAR ("tree" . "r0") . 0))
                        (8 . "r0"))
                       (((8 :VAR ("tree" . "r1") . 0))
                        (8 . "r1"))
                       (((8 :VAR ("tree" . "r2") . 0))
                        (8 . "r2"))
                       (((8 :VAR ("tree" . "r3") . 0))
                        (8 . "r3"))
                       (((8 :VAR ("tree" . "result") . 0))
                        (8 "res2" . 6))))))
     (fast-alist-clean alist))

||#

(defun fix-module-occs-port-order (cur-ports module-ports)
  (if (atom module-ports)
      nil
    (cons (assoc-equal (car module-ports) cur-ports)
          (fix-module-occs-port-order cur-ports (cdr module-ports)))))

(defun sv->svl-insts (aliaspairs-alist vl-insouts insts)
  (declare (xargs :mode :program))
  ;; Goal for every instantiation in a module, create an DE-like occurance list
  ;; differentiating between input and output. Every entry in the returned alist
  ;; will have the following format:
  ;; (occ-name (inputs) (outputs) module-name)
  ;; where each input is of the form ((mod-sig-name mod-sig-size mod-sig-start)
  ;; . (sig-name sig-size sig-start))
  (if (atom insts)
      nil
    (b* ((c (car insts))
         (occ-name (car c))
         (module (cdr c))
         ((when (not (stringp module)))
          (case-match module
            ((this-mod-name :genarray arr-name)
             (hard-error
              'sv->svl-insts
              "Don't know what to do with a genarray inst. ~% (~p0 :genarray ~p1) ~%"
              (list (cons #\0 this-mod-name)
                    (cons #\1 arr-name))))
            (& (progn$
                (cw "WARNING: Module name (~p0) is not recognized. Skipping... ~%"
                    module)
                (sv->svl-insts aliaspairs-alist vl-insouts
                               (cdr insts))))))
         (module-insouts (assoc-equal module vl-insouts))
         ((unless module-insouts)
          (progn$
           (cw "WARNING: Module name (~p0) cannot be found in vl-insouts  ~
  list. Skipping... ~%" module vl-insouts)
           (sv->svl-insts aliaspairs-alist vl-insouts
                          (cdr insts))))
         (module-ins (cadr module-insouts))
         (module-outs (cddr module-insouts))
         (aliases (hons-get occ-name aliaspairs-alist))
         ((mv ins outs)
          (sv->svl-get-insouts-for-occ occ-name
                                       module-ins
                                       module-outs
                                       (cdr aliases)))
         ;; make-sure-ports-are-in-order
         (ins (fix-module-occs-port-order ins module-ins))
         (outs (fix-module-occs-port-order outs module-outs)))
      (hons-acons occ-name
                  (make-occ-module :inputs ins
                                   :outputs outs
                                   :name module)
                  (sv->svl-insts aliaspairs-alist vl-insouts
                                 (cdr insts))))))

(defun sv->svl-assigns-vars-clear (all-vars)
  (declare (xargs :mode :program))
  (if (atom all-vars)
      (mv nil nil)
    (b* (((mv rest-cur rest-prev) (sv->svl-assigns-vars-clear (cdr all-vars)))
         (first (car all-vars)))
      (case-match first
        ((':VAR val . delay)
         (cond ((= delay 1)
                (mv rest-cur (cons val rest-prev)))
               ((integerp delay)
                (mv (hard-error 'sv->svl-assigns-vars-clear
                                "Unexpected delay value in assignment! ~%" nil)
                    nil))
               (t (mv (cons val rest-cur) rest-prev))))
        (&
         (mv (cons first rest-cur)
             rest-prev))))))

(defun sv->svl-assigns-vars (svex)
  (declare (xargs :mode :program))
  (b* ((all-vars (sv::svex-vars svex)))
    (sv->svl-assigns-vars-clear all-vars)))

(defun sv->svl-assigns-fix-sigs (assign-outs)
  (declare (xargs :mode :program))
  (if (atom assign-outs)
      nil
    (b* ((out (car assign-outs))
         (fixed
          (case-match out
            ((size ':VAR name . start)
             (cond
              ((and (integerp size)
                    (integerp start))
               `(,name ,size . ,start))
              (t
               (progn$
                (cw "Working on: ~p0, name=~p1, start=~p2, size=~p3 ~%"
                    out name start size)
                (hard-error 'sv->svl-assigns-fix-sigs
                            "Unexpected assignment output signal ~%"
                            nil)))))
            ((':VAR name . start)
             (cond
              ((and (integerp start)
                    (or (stringp name)
                        (and (consp name)
                             (stringp (car name))
                             (stringp (cdr name)))))
               (b* ((name (if (stringp name) name
                            (intern$ (str::cat (car name) "$" (cdr name))
                                     *package-name*))))
                 `(,name 1 . ,start)))
              (t
               (progn$
                (cw "Working on: ~p0, name=~p1, start=~p2, size=~p3 ~%"
                    out name start 1)
                (hard-error 'sv->svl-assigns-fix-sigs
                            "Unexpected assignment output signal ~%"
                            nil)))))
            ((size ':VAR name)
             (cond
              ((and (integerp size))
               `(,name ,size . 0))
              (t
               (progn$
                (cw "Working on: ~p0, name=~p1, start=~p2, size=~p3  ~%"
                    out name 0 size)
                (hard-error 'sv->svl-assigns-fix-sigs
                            "Unexpected assignment output signal ~%"
                            nil)))))
            ((size name . start)
             (cond
              ((and (stringp name)
                    (integerp size)
                    (integerp start))
               `(,name ,size . ,start))
              (t
               (progn$
                (cw "Working on: ~p0, name=~p1, start=~p2, size=~p3  ~%"
                    out name start size)
                (hard-error 'sv->svl-assigns-fix-sigs
                            "Unexpected assignment output signal ~%"
                            nil)))))
            ((size . name)
             (if (integerp size)
                 `(,name ,size . 0)
               `(,size 1 . ,name))) ;; then it is (name . start)
            (& `(,out 1 . 0)))))
      (cons fixed
            (sv->svl-assigns-fix-sigs (cdr assign-outs))))))

(defun sv->svl-assigns-fix-sigs-? (assign-outs)
  (declare (xargs :mode :program))
  (if (atom assign-outs)
      nil
    (b* ((out (car assign-outs))
         (fixed `(,out ? . ?)))
      (cons fixed
            (sv->svl-assigns-fix-sigs-? (cdr assign-outs))))))

(defun svex-find-size-of-var-grow (old-start old-size sug-start sug-size)
  (declare (xargs :mode :program))
  (if (or (not (integerp old-size))
          (not (integerp old-start)))
      (cons sug-size sug-start)
    (b* ((old-end (+ old-start old-size))
         (sug-end (+ sug-size sug-start)))
      (cond ((and (< sug-start old-start)
                  (< sug-end old-end))
             (cons (- old-end sug-start) sug-start))
            ((and (< sug-start old-start)
                  (>= sug-end old-end))
             (cons (- sug-end sug-start) sug-start))
            ((and (>= sug-start old-start)
                  (< sug-end old-end))
             (cons (- old-end old-start) old-start))
            (t
             (cons (- sug-end old-start) old-start))))))

(defun svex-find-size-of-var (svex var size start orig-size)
  (declare (xargs :mode :program))
  ;; Goal look at an svex whose one of inputs is var. Try to find the start and
  ;; end positions. Orig-size is the size as determined by the wires list.
  ;; this is just to give an approximate result. But it should never give a
  ;; subset of the input vector.
  (cond
   ((integerp svex)
    (cons size start))
   ((stringp svex)
    (if (equal svex var)
        (cons orig-size 0)
      (cons size start)))
   (t
    (case-match svex
      ((':VAR & . &)
       (cons size start))
      (('SV::PARTSEL start-arg size-arg ('SV::CONCAT & arg3 ''(-1 . 0)))
       (if (equal arg3 var)
           (svex-find-size-of-var-grow start size start-arg size-arg)
         (svex-find-size-of-var arg3 var size start  orig-size)))
      (('SV::PARTSEL start-arg size-arg arg3)
       (if (equal arg3 var)
           (svex-find-size-of-var-grow start size start-arg size-arg)
         (svex-find-size-of-var arg3 var size start  orig-size)))
      ((& arg0 arg1 arg2)
       (b* ((result (svex-find-size-of-var arg0 var size start  orig-size))
            (result (svex-find-size-of-var arg1 var (car result) (cdr result)  orig-size)))
         (svex-find-size-of-var arg2 var (car result) (cdr result)  orig-size)))
      ((& arg1 arg2)
       (b* ((result (svex-find-size-of-var arg1 var size start  orig-size)))
         (svex-find-size-of-var arg2 var (car result) (cdr result)  orig-size)))
      ((& arg1)
       (if (equal arg1 var)
           (svex-find-size-of-var-grow start size 0 1)
         (svex-find-size-of-var arg1 var size start  orig-size)))
      (&
       (cw "something went wrong... ~%"))))))

(defun svex-find-size-of-vars (svex vars wires)
  (declare (xargs :mode :program))
  (if (atom vars)
      nil
    (b* ((wire (assoc-equal (car vars) wires))
         (- (if wire nil
              (progn$
               (cw "Var= ~p0, Wires= ~p1 ~%" (car vars) wires)
               (hard-error 'svex-find-size-of-vars
                           "Wire cannot be Found! ~%"
                           nil))))
         (orig-size (wire-size wire)))
      (cons (list* (car vars)
                   (svex-find-size-of-var svex (car vars) '? '? orig-size))
            (svex-find-size-of-vars svex (cdr vars) wires)))))

(defun sv->svl-assigns (assigns cnt wires)
  (declare (xargs :mode :program))
  (if (atom assigns)
      nil
    (b* ((assign (car assigns))
         (svex (cadr assign))
         (outs (sv->svl-assigns-fix-sigs (car assign)))
         ;; get the variables from svex
         ((mv cur-ins prev-ins)
          (sv->svl-assigns-vars svex))
         #|(ins (sv->svl-assigns-fix-sigs-? cur-ins))||#
         (ins (svex-find-size-of-vars svex cur-ins wires))
         (cur (cons (sa 'assign cnt)
                    (make-occ-assign
                     :inputs ins
                     :delayed-inputs prev-ins
                     :outputs outs
                     :svex svex))))
      (cons
       cur
       (sv->svl-assigns (cdr assigns) (1+ cnt) wires)))))

(defun sv->svl-create-signal-listeners-aux (occ-name occ-type occ-ins alist)
  (if (atom occ-ins)
      alist
    (b* ((cur (car occ-ins))
         (signame (if (equal occ-type ':assign) (car cur) (cadr cur)))
         (e (hons-get signame alist)))
      (sv->svl-create-signal-listeners-aux
       occ-name occ-type (cdr occ-ins)
       (hons-acons signame
                   (cons occ-name (if e (cdr e) nil))
                   alist)))))

(defun sv->svl-create-signal-listeners (occs)
  ;; create listeners where each key is a signal name and each val is a list of
  ;; occurances. Whenever that a signal changes corresponding occurances should
  ;; probably run
  (if (atom occs)
      nil
    (b* ((occ (car occs))
         (occ-name (car occ))
         (occ (cdr occ))
         (occ-type (occ-kind occ))
         (occ-ins (if (equal occ-type ':assign) (occ-assign->inputs occ) (occ-module->inputs occ)))
         (alist (sv->svl-create-signal-listeners (cdr occs)))
         (alist (sv->svl-create-signal-listeners-aux occ-name occ-type occ-ins alist)))
      alist)))

(defun sv->svl-create-occ-listeners-count-matches-aux (occ-out other-occ-ins)
  (if (atom other-occ-ins)
      0
    (b* ((other (car other-occ-ins))
         ((unless (equal (car other)
                         (if (consp occ-out) (car occ-out) occ-out)))
          (sv->svl-create-occ-listeners-count-matches-aux occ-out
                                                          (cdr other-occ-ins)))
         ;; check for overlap:
         (o-size (cadr other))
         (o-start (cddr other))
         (size (if (consp occ-out) (cadr occ-out) nil))
         (start (if (consp occ-out) (cddr occ-out) nil))
         ((when (or (not o-start)
                    (not start)))
          (+ 1
             (sv->svl-create-occ-listeners-count-matches-aux occ-out
                                                             (cdr other-occ-ins))))
         (o-end (+ o-start o-size))
         (end (+ size start)))
      (+ (if (or (and (<= o-start start)
                      (< start o-end))
                 (and (<= start o-start)
                      (< o-start end)))
             1 0)
         (sv->svl-create-occ-listeners-count-matches-aux occ-out
                                                         (cdr other-occ-ins))))))

(defun sv->svl-create-occ-listeners-count-matches (occ-outs other-occ-ins)
  (declare (xargs :mode :program))
  (if (atom occ-outs)
      0
    (+
     (sv->svl-create-occ-listeners-count-matches-aux (car occ-outs)
                                                     other-occ-ins)
     (sv->svl-create-occ-listeners-count-matches (cdr occ-outs)
                                                 other-occ-ins))))

(defun sv->svl-create-occ-listeners-aux (occ-outs all-occs relevant-occ-names)
  ;; returned is a list of pairs aka alist.  keys are occ names and vals are a
  ;; score assigned to them.  This score will be used to sort the occs in a
  ;; listener. The higher the better. This is equal to the negative number of
  ;; missing signals that the owner occ of this listener covers in the other
  ;; occs

  (declare (xargs :mode :program))
  (if (atom relevant-occ-names)
      nil
    (b* ((cur (hons-get (caar relevant-occ-names) all-occs))
         (occ (cdr cur))
         (other-occ-type (occ-kind occ))
         (other-occ-ins
          (if (equal other-occ-type ':assign)
              (occ-assign->inputs occ)
            (occ-module->inputs occ)))
         (other-occ-ins (if (equal other-occ-type ':module)
                            (strip-cdrs other-occ-ins)
                          other-occ-ins))
         (other-name (car cur))
         (matches (sv->svl-create-occ-listeners-count-matches occ-outs
                                                              other-occ-ins))
         (rest (sv->svl-create-occ-listeners-aux occ-outs all-occs (cdr relevant-occ-names))))
      (if (> matches 0)
          (cons (cons other-name (- matches (len other-occ-ins)))  rest)
        rest))))

(defun fast-alist-unique-append-keys (keys alist)
  (if (atom keys)
      alist
    (fast-alist-unique-append-keys
     (cdr keys)
     (if (hons-get (car keys) alist)
         alist
       (hons-acons (car keys) nil alist)))))

(defun sv->svl-listeners-get-relevant-occs (occ-sigs full-signal-listeners)
  (if (atom occ-sigs)
      nil
    (b* ((cur-name (car occ-sigs))
         (cur-name (if (consp cur-name) (car cur-name) cur-name))
         (occ-names (cdr (hons-get cur-name full-signal-listeners)))
         (rest (sv->svl-listeners-get-relevant-occs (cdr occ-sigs)
                                                    full-signal-listeners))
         ((unless occ-names) rest))
      (fast-alist-unique-append-keys occ-names rest))))

(defmacro listener-comperator (x y)
  ;; we use this comperator to order pairs generated by
  ;; sv->svl-create-occ-listeners-aux
  `(>= (cdr ,x)
       (cdr ,y)))

;(defwarrant listener-comperator)

(defun merge-listener-comperator (l1 l2 acc)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2)
                              (true-listp acc))
                  :verify-guards nil
                  :measure (+ (len l1) (len l2))))
  (cond ((endp l1) (revappend acc l2))
        ((endp l2) (revappend acc l1))
        ((listener-comperator (car l1) (car l2))
         (merge-listener-comperator (cdr l1)
                           l2 (cons (car l1) acc)
                           ))
        (t (merge-listener-comperator l1 (cdr l2)
                             (cons (car l2) acc)))))

(defun merge-listener-sort (l)
  (declare (xargs :guard (and (true-listp l))
                  :measure (len l)
                  :mode :program 
                  :verify-guards nil))
  (cond ((endp (cdr l)) l)
        (t (merge-listener-comperator (merge-listener-sort (evens l))
                                      (merge-listener-sort (odds l))
                                      nil))))

(defun sv->svl-create-occ-listeners-aux2 (occ-outs all-occs relevant-occ-names)
  (declare (xargs :mode :program))
  (b* (;; sv->svl-create-occ-listeners-aux returns a list of pairs aka an alist
       ;; keys are other-occ-names and vals are their score.  their scores are
       ;; bigger if the output signal of this occ covers more of the other-occs
       ;; inputs
       (entry (sv->svl-create-occ-listeners-aux occ-outs all-occs
                                                relevant-occ-names))
       ;; we order this entry by the score and take the keys only.
       (entry (merge-listener-sort entry))
       (entry (strip-cars entry)))
    entry))

(defun sv->svl-create-occ-listeners (occs all-occs full-signal-listeners)
  ;; Create listeners where each key is an occ name and each val is occ name
  ;; list.  Whenever an occ runs, every occurance in its corresponding occ list
  ;; should also run.  It uses previously created signal listeners created by
  ;; sv->svl-create-signal-listeners. Doing this helps a lot with the
  ;; performance for big circuits.

  (declare (xargs :mode :program))
  (if (atom occs)
      nil
    (b* ((occ (car occs))
         (occ-name (car occ))
         (occ (cdr occ))
         (occ-type (occ-kind occ))
         (occ-outs (if (equal occ-type ':assign)
                       (occ-assign->outputs occ)
                     (strip-cdrs (occ-module->outputs occ))))
         ;; get occ-names that will possibly need to be run after the current
         ;; occurance.
         ;; it is a fast-alist for quick lookup while adding to prevent
         ;; repitition.
         ;; every key is occ-name
         (relevant-occ-names
          (sv->svl-listeners-get-relevant-occs occ-outs full-signal-listeners))
         ;; get the entry for current occ. It is ordered with respect to
         ;; coverage of this occ's outputs in other-occs' inputs.
         (entry (sv->svl-create-occ-listeners-aux2 occ-outs all-occs relevant-occ-names))
         (- (fast-alist-free relevant-occ-names))
         ;; rest of the listeners:
         (alist (sv->svl-create-occ-listeners (cdr occs) all-occs full-signal-listeners)))
      (if entry
          (hons-acons occ-name entry alist)
        alist))))

(defun sv->svl-listeners-uncovered-occs-get-added-occs-aux (occs alist)
  (declare (xargs :mode :program))
  (if (atom occs)
      alist
    (sv->svl-listeners-uncovered-occs-get-added-occs-aux
     (cdr occs)
     (if (hons-get (car occs) alist)
         alist
       (hons-acons (car occs) nil alist)))))

(defun sv->svl-listeners-uncovered-occs-get-added-occs (listeners)
  (declare (xargs :mode :program))
  (if (atom listeners)
      nil
    (sv->svl-listeners-uncovered-occs-get-added-occs-aux
     (cdar listeners)
     (sv->svl-listeners-uncovered-occs-get-added-occs (cdr listeners)))))

(defun sv->svl-listeners-get-missing-occs (added all)
  (declare (xargs :mode :program))
  (if (atom all)
      nil
    (b* ((rest (sv->svl-listeners-get-missing-occs added (cdr all))))
      (if (hons-get (car (car all)) added)
          rest
        (cons (car (car all))
              rest)))))

(defun sv->svl-listeners-uncovered-occs (listeners all-occs)
  (declare (xargs :mode :program))
  ;; get the names of the unrefered occs by any listener in the listeners list.
  ;; they need to be executed initially because they may drive constants or something.
  (b* ((added-occs (sv->svl-listeners-uncovered-occs-get-added-occs
                    listeners))
       ;; added-occs is a fast-alist for quick membership lookup.
       (unadded-occs (sv->svl-listeners-get-missing-occs added-occs all-occs)))
    (progn$
     (fast-alist-free added-occs)
     unadded-occs)))

(defun sv->svl-add-initial-listeners (main-inputs listeners all-occs full-signal-listeners)
  (declare (xargs :mode :program))
  (b* ((relevant-occ-names
        (sv->svl-listeners-get-relevant-occs main-inputs
                                             full-signal-listeners))
       (entry (sv->svl-create-occ-listeners-aux2 main-inputs all-occs
                                                 relevant-occ-names))
       (uncovered-occs
        (sv->svl-listeners-uncovered-occs (cons (cons ':initial entry) listeners)
                                          all-occs))
       (entry (append entry uncovered-occs))
       (- (fast-alist-free relevant-occ-names)))
    (hons-acons ':initial entry listeners)))

(encapsulate
  nil

  (defun add-to-fast-alist-unique (keys vals alist)
    (declare (xargs :mode :program))
    (if (atom keys)
        alist
      (if (hons-get (car keys) alist)
          (add-to-fast-alist-unique (cdr keys) (cdr vals)
                                    alist)
        (hons-acons (car keys) (car vals)
                    (add-to-fast-alist-unique (cdr keys) (cdr vals)
                                              alist)))))

  (defun union-entries-of-fast-alist  (keys alist)
    (declare (xargs :mode :program))
    (if (atom keys)
        nil
      (let ((entry (hons-get (car keys) alist)))
        (add-to-fast-alist-unique entry #|(if entry entry (list (car keys)))||#
                                  nil
                                  (union-entries-of-fast-alist (cdr keys) alist)))))

  (mutual-recursion
   (defun shrink-occ-listeners-would-calls (occ-name trace orig-listeners acc)
     (declare (xargs :mode :program)
              (ignorable trace))
     (if (or  (hons-get occ-name acc)
              (member-equal occ-name trace))
         acc
       (b* ((trace (cons occ-name trace))
;(acc (hons-acons occ-name nil acc))
            (other-occs (cdr (hons-get occ-name orig-listeners)))
            (acc (shrink-occ-listeners-would-calls-lst
                  other-occs
                  trace
                  orig-listeners
                  acc))
            (entry (fast-alist-free
                    (union-entries-of-fast-alist other-occs acc)))
            (entry (strip-cars entry)))
         (hons-acons occ-name entry acc))))

   (defun shrink-occ-listeners-would-calls-lst (occ-lst trace orig-listeners
                                                        acc)
     (declare (xargs :mode :program)
              (ignorable trace))
     (if (atom occ-lst)
         acc
       (shrink-occ-listeners-would-calls-lst
        (cdr occ-lst) trace orig-listeners
        (shrink-occ-listeners-would-calls (car occ-lst) trace orig-listeners acc)))))

  #|(shrink-occ-listeners-would-calls
  ':initial nil
  (make-fast-alist '((:initial a b d)
  (a b c)
  (b a c)
  (d a)))
  nil)||#

  (defun member-wrap (x y)
    (declare (xargs :mode :program))
    (member-equal x y))

  (defun sv->svl-shrink-occ-listeners-each-aux (occ-names cur-would-calls
                                                          would-call-alist
                                                          visited)
    (declare (xargs :mode :program))
    (if (atom occ-names)
        (progn$
         (fast-alist-free visited)
         nil)
      (b* ((cur (car occ-names))
           ((when (hons-get cur visited))
            (sv->svl-shrink-occ-listeners-each-aux (cdr occ-names)
                                                   cur-would-calls
                                                   would-call-alist
                                                   visited))
           ((unless (hons-get cur cur-would-calls))
            (cons cur
                  (sv->svl-shrink-occ-listeners-each-aux (cdr occ-names)
                                                         cur-would-calls
                                                         would-call-alist
                                                         (hons-acons cur nil visited))))
           (visited (add-to-fast-alist-unique (hons-get cur would-call-alist)
                                              nil
                                              visited)))
        (cons cur
              (sv->svl-shrink-occ-listeners-each-aux (cdr occ-names)
                                                     cur-would-calls
                                                     would-call-alist
                                                     visited)))))

  (defun sv->svl-shrink-occ-listeners-each (orig-listeners would-call-alist)
    (declare (xargs :mode :program))
    (if (atom orig-listeners)
        nil
      (b* ((cur (car orig-listeners))
           (cur-name (car cur))
           (cur-list (cdr cur))
           (cur-would-calls (cdr (hons-get cur-name would-call-alist)))
           (cur-would-calls (add-to-fast-alist-unique cur-would-calls nil
                                                      (* 2 (len cur-would-calls))))
           (new-listener-occs (sv->svl-shrink-occ-listeners-each-aux
                               cur-list
                               cur-would-calls
                               would-call-alist
                               nil))
           (- (fast-alist-free cur-would-calls)))
        (hons-acons cur-name
                    new-listener-occs
                    (sv->svl-shrink-occ-listeners-each (cdr orig-listeners)
                                                       would-call-alist)))))

  (defun sv->svl-shrink-occ-listeners (orig-listeners)
    (declare (xargs :mode :program))
    (b* ((orig-listeners (make-fast-alist orig-listeners))
         (would-call-alist
          (shrink-occ-listeners-would-calls ':initial nil
                                            orig-listeners nil))
         (- (fast-alist-free orig-listeners))
         (listeners (sv->svl-shrink-occ-listeners-each orig-listeners
                                                       would-call-alist)))
      listeners))

  #|(sv->svl-shrink-occ-listeners
  ;; keep this example to understand the functions.
  (make-fast-alist '((:initial a b c d)
  (a b c)
  (b a d c)
  (d a c)))
  )||#
  )

(defun svl-to-fast-alist (alist)
  (declare (xargs :guard (alistp alist)))
  (if (atom alist)
      nil
    (hons-acons (caar alist)
                (cdar alist)
                (svl-to-fast-alist (cdr alist)))))

(defun sv->svl-attach-wire-sizes (sigs wire-sizes)
  (if (atom sigs)
      sigs
    (cons (hons-get (car sigs) wire-sizes)
          (sv->svl-attach-wire-sizes (cdr sigs)
                                     wire-sizes))))

(defun sv->svl-module (sv-module vl-insouts)
  (declare (xargs :mode :program))
  ;; For a module calls sv->svl-insts and sv->svl-assigns to create a
  ;; DE-like structure.
  (b* ((module-name (car sv-module))
       ((unless (stringp module-name))
        nil)
       (sv-module (cdr sv-module))
       (aliaspairs (cdr (assoc-equal 'sv::aliaspairs sv-module)))
       (insts (cdr (assoc-equal 'sv::insts sv-module)))
       (assigns (cdr (assoc-equal 'sv::assigns sv-module)))
       (wires (strip-cars (cdr (assoc-equal 'sv::wires sv-module))))
       ;; returns the wire alist with keys as wire names and entries as wire
       ;; sizes. Every wire starts from 0 by default.
       ;; result is a fast-alist
       (wires (sv->svl-get-wire-sizes wires))
       ((Unless (wire-list-p wires))
        (progn$ (cw "Wire-list is strange skipping the module.. ~p0 ~p1 ~%"
                    module-name wires)
                nil))

       ;; get inputs and output signals of the module.
       (module-insouts (assoc-equal module-name vl-insouts))
       (module-ins (cadr module-insouts))
       (module-outs (cddr module-insouts))

       ;; seperate aliaspairs with respect to occurances.
       ;; create an alist for it.
       ;; every key is occ-name, and every entry is an aliaspair list.
       (aliaspairs-alist
        (fast-alist-clean
         (sv->svl-aliaspairs-to-alist aliaspairs)))

       ;; create the module occurances from instantiation lists
       (occ-from-insts (sv->svl-insts aliaspairs-alist
                                      vl-insouts
                                      insts))
       (- (fast-alist-free aliaspairs-alist))
       (- (fast-alist-free occ-from-insts))
       ;; creaate assignment occurances
       (occ-from-assigns (sv->svl-assigns (acl2::rev assigns) 0 wires))
       ;; merge the two occurance list
       (occs (svl-to-fast-alist
              (append occ-from-insts
                      occ-from-assigns)))

       ;; create an auxilary signal listener structure. It is an alist where
       ;; every key is a signal name and entries are occ names. Whenever a
       ;; signal in the keys changes, corresponding occurances should be run.
       ;; Creating the final listeners becomes faster when
       ;; full-signal-listeners is used.
       (full-signal-listeners (sv->svl-create-signal-listeners occs))

       ;; Create another and final listener structure. Every keys are occurance
       ;; names and entries are also occurance names. Whenever an occurance in
       ;; the keys are run, the corresponding occurances in the entries should
       ;; also be run.
       (listeners (sv->svl-create-occ-listeners occs occs full-signal-listeners))

       ;; initial listeners. When this module is called, we need to run these
       ;; occurances initially. It may be because they have the module's input
       ;; signals going into them, or they are not added to the queue at any
       ;; time so we add them initially to make sure that they run at least once.
       (listeners (sv->svl-add-initial-listeners (cadr module-insouts)
                                                 listeners
                                                 occs
                                                 full-signal-listeners))
       (listeners (sv->svl-shrink-occ-listeners listeners))
       (- (fast-alist-free full-signal-listeners)))
    (cons module-name
          (make-svl-module
           :inputs module-ins
           :delayed-inputs nil
           :outputs module-outs
           :wires wires
           :occs occs
           :listeners listeners))))

(defun sv->svl-per-module (sv-modules vl-insouts)
  (declare (xargs :mode :program))
  (if (atom sv-modules)
      nil
    (b* ((module (sv->svl-module (car sv-modules)
                                 vl-insouts))
         (- (fast-alist-free (SVL-module->occs (cdr module)))) ;;BREAKING 
         (- (fast-alist-free (SVL-module->listeners (cdr module))))
         ) ;; BREAKING
      (if module
          (cons
           module
           (sv->svl-per-module (cdr sv-modules)
                               vl-insouts))
        (sv->svl-per-module (cdr sv-modules)
                            vl-insouts)))))

(defun get-max (lst)
  (if (atom lst)
      0
    (max (car lst)
         (get-max (cdr lst)))))

(acl2::defines
 svl-calculate-rank
 (define svl-calculate-rank (module-name  rank-alist limit svl-modules)
   (declare (xargs :mode :program))
   (if (zp limit)
       (progn$ (cw "Limit Reached! ~%")
               (mv rank-alist 0))
     (b* ((module-entry (hons-get module-name svl-modules))
          ((unless module-entry)
           (progn$ (hard-error 'svl-calculate-rank
                               "Module could not be found! ~%" nil)
                   (mv rank-alist 0)))
          (module (cdr module-entry))
          (occs (svl-module->occs module))
          ((mv rank-alist occs-ranks)
           (svl-calculate-rank-occs occs rank-alist (1- limit) svl-modules))
          (rank (1+ (get-max occs-ranks))))
       (mv (hons-acons module-name rank rank-alist) rank))))

 (define svl-calculate-rank-occs (occs rank-alist limit svl-modules)
   (if (atom occs)
       (mv rank-alist nil)
     (b* (((mv rank-alist rest)
           (svl-calculate-rank-occs (cdr occs) rank-alist limit svl-modules))
          ((unless (equal (occ-kind (cdar occs))
                          ':module))
           (mv rank-alist rest))
          (occ-module-name (occ-module->name (cdar occs)))
          (rank-entry (hons-get occ-module-name rank-alist))
          ((mv rank-alist occ-rank)
           (if rank-entry
               (mv rank-alist (cdr rank-entry))
             (svl-calculate-rank occ-module-name rank-alist limit
                                 svl-modules))))
       (mv rank-alist (cons occ-rank rest))))))

(encapsulate
  nil

  (defun sv->svl-get-delayed-ins-1st-pass-aux (svl-occs)
    (if (atom svl-occs)
        nil
      (b* ((occ (cdar svl-occs))
           ((unless (and (equal (occ-kind occ) ':assign)
                         (occ-assign->delayed-inputs occ)))
            (sv->svl-get-delayed-ins-1st-pass-aux (cdr svl-occs))))
        (union$ (occ-assign->delayed-inputs occ)
                (sv->svl-get-delayed-ins-1st-pass-aux (cdr svl-occs))
                :test 'equal))))

  (defun sv->svl-get-delayed-ins-1st-pass (svl-modules)
    (if (atom svl-modules)
        nil
      (cons
       #|(caar svl-modules)||#
       (sv->svl-get-delayed-ins-1st-pass-aux (svl-module->occs (cdar svl-modules)))
       (sv->svl-get-delayed-ins-1st-pass (cdr svl-modules)))))

  ;; (defun sv->svl-get-delayed-ins-2nd-pass-aux (svl-occs first-pass-results)
  ;;   (if (atom svl-occs)
  ;;       nil
  ;;     (b* ((occ (cdar svl-occs))
  ;;          ((unless (and (equal (occ-kind occ)
  ;;                               ':module)
  ;;                        (cdr (hons-get (occ-module->name occ) first-pass-results))))
  ;;           (sv->svl-get-delayed-ins-2nd-pass-aux (cdr svl-occs) first-pass-results)))
  ;;       (cons (cons (caar svl-occs) (occ-module->name occ))
  ;;             (sv->svl-get-delayed-ins-2nd-pass-aux (cdr svl-occs) first-pass-results)))))

  ;;; !!!!!!!!!!!!!!!!!
  ;; ;; this needs to be fixed. what if a module does not have any delayed inputs
  ;; ;; for assignments but its submodules need delayed inputs? then this will fail.
  ;; ;; !!!!!!!!!!!!!
  ;; ;; MAYBE NOT... COMMMENTS NEED TO BE UPDATED
  ;; (defun sv->svl-get-delayed-ins-2nd-pass (svl-modules first-pass-results)
  ;;   (if (atom svl-modules)
  ;;       nil
  ;;     (b* ((aux-res (sv->svl-get-delayed-ins-2nd-pass-aux
  ;;                    (svl-occs (cdar svl-modules))
  ;;                    first-pass-results))
  ;;          (first-pass (cdr (hons-get (caar svl-modules) first-pass-results))))
  ;;       (acons
  ;;        (caar svl-modules)
  ;;        (if (or aux-res first-pass) (cons first-pass aux-res) nil)
  ;;        (sv->svl-get-delayed-ins-2nd-pass (cdr svl-modules) first-pass-results)))))

  (defun sv->svl-add-delayed-ins-and-ranks-aux (svl-modules ranks-alist first-pass-results)
    (if (atom svl-modules)
        nil
      (hons-acons
       (caar svl-modules)
       (change-svl-module (cdar svl-modules)
                          :rank (cdr (hons-get (caar svl-modules) ranks-alist))
                          :delayed-inputs (car first-pass-results)
                          #|(make-delayed-inputs
                          :modules (cddar second-pass-res)
                          :wire-names (cadar second-pass-res))||#)
       (sv->svl-add-delayed-ins-and-ranks-aux (cdr svl-modules)
                                              ranks-alist
                                              (cdr first-pass-results)))))

  (defun sv->svl-add-delayed-ins-and-ranks (svl-modules top-module-name)
    (declare (xargs :mode :program))
    (b* ((first-pass-results (sv->svl-get-delayed-ins-1st-pass svl-modules))
         #|(second-pass-res
         (sv->svl-get-delayed-ins-2nd-pass svl-modules first-pass-res))||#
         #|(- (fast-alist-free first-pass-res))||#
         (svl-modules (make-fast-alist svl-modules))
         ((mv ranks-alist &)
          (svl-calculate-rank top-module-name nil
                              (len svl-modules)
                              svl-modules))
         (- (fast-alist-free svl-modules))
         (res (sv->svl-add-delayed-ins-and-ranks-aux svl-modules
                                                     ranks-alist
                                                     first-pass-results))
         (- (fast-alist-free res)) ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; BREAKING
         (- (fast-alist-free ranks-alist)))
      res)))

(defun sv->svl (sv-design vl-design)
  (declare (xargs :mode :program))
  (b* ((vl-insouts (vl-design-to-insouts vl-design sv-design))
       (sv-modules (cdr (assoc-equal 'sv::modalist sv-design)))
       (svl-modules (sv->svl-per-module sv-modules vl-insouts))
       (top-module-name (cdr (assoc-equal 'sv::TOP sv-design)))
       (svl-modules (sv->svl-add-delayed-ins-and-ranks svl-modules top-module-name)))
    svl-modules))

#|

(b* ((module '("mul_test1" (SV::WIRES (("mr" 4 . 0))
                                      (("md" 4 . 0))
                                      (("result" 8 . 0))
                                      (("x" 4 . 0))
                                      (("z" 4 . 0))
                                      (("r0" 8 . 0))
                                      (("r1" 8 . 0))
                                      (("r2" 8 . 0))
                                      (("r3" 8 . 0))
                                      (("res2" 16 . 0)))
               (SV::INSTS ("booth" . "booth_encoder")
                          ("pp" . "partial")
                          ("tree" . "wallace"))
               (SV::ASSIGNS
                (((8 . "result"))
                 (SV::ZEROX 8
                            (SV::PARTSEL 6 8 (SV::CONCAT 16 "res2" '(-1 . 0))))
                 . 6))
               (SV::FIXUPS)
               (SV::CONSTRAINTS)
               (SV::ALIASPAIRS (((4 :VAR ("booth" . "mr") . 0))
                                (4 . "mr"))
                               (((4 :VAR ("booth" . "md") . 0))
                                (4 . "md"))
                               (((4 :VAR ("booth" . "x") . 0))
                                (4 . "x"))
                               (((4 :VAR ("booth" . "z") . 0))
                                (4 . "z"))
                               (((4 :VAR ("pp" . "x") . 0)) (4 . "x"))
                               (((4 :VAR ("pp" . "z") . 0)) (4 . "z"))
                               (((8 :VAR ("pp" . "r0") . 0))
                                (8 . "r0"))
                               (((8 :VAR ("pp" . "r1") . 0))
                                (8 . "r1"))
                               (((8 :VAR ("pp" . "r2") . 0))
                                (8 . "r2"))
                               (((8 :VAR ("pp" . "r3") . 0))
                                (8 . "r3"))
                               (((4 :VAR ("pp" . "md") . 0))
                                (4 . "md"))
                               (((4 :VAR ("pp" . "mr") . 0))
                                (4 . "mr"))
                               (((8 :VAR ("tree" . "r0") . 0))
                                (8 . "r0"))
                               (((8 :VAR ("tree" . "r1") . 0))
                                (8 . "r1"))
                               (((8 :VAR ("tree" . "r2") . 0))
                                (8 . "r2"))
                               (((8 :VAR ("tree" . "r3") . 0))
                                (8 . "r3"))
                               (((8 :VAR ("tree" . "result") . 0))
                                (8 "res2" . 6)))))
     (vl-insouts *booth-insouts*))
  (sv->svl-module module vl-insouts))

||#

(encapsulate
  nil
  (mutual-recursion
   (defun svl-listeners-loopfreep-aux (occ-name trace listeners)
     (declare (xargs :mode :program))
     (if (member-equal occ-name trace)
         (cw "Occ = ~p0 gets in a loop. Trace=~p1 ~%" occ-name trace)
       (svl-listeners-loopfreep-aux-list (cdr (hons-get occ-name listeners))
                                         (cons occ-name trace)
                                         listeners)))

   (defun svl-listeners-loopfreep-aux-list (occ-name-lst trace listeners)
     (if (atom occ-name-lst)
         t
       (and (svl-listeners-loopfreep-aux (car occ-name-lst) trace listeners)
            (svl-listeners-loopfreep-aux-list (cdr occ-name-lst) trace listeners)))))

  (defun svl-listeners-loopfreep (listeners)
    (declare (xargs :mode :program))
    (svl-listeners-loopfreep-aux ':initial nil listeners))

  (defun svl-loopfreep (svl-design)
    (declare (xargs :mode :program))
    (if (atom svl-design)
        t
      (and (or (svl-listeners-loopfreep (svl-listeners (car svl-design)))
               (cw "Loop in module = ~p0 ~%" (caar svl-design)))
           (svl-loopfreep (cdr svl-design))))))


 
(defun cons-deep-copy (term)
  (declare (xargs :guard t))
  (cond ((atom term) term)
        ((quotep term) term)
        (t (cons (cons-deep-copy (car term))
                 (cons-deep-copy (cdr term))))))

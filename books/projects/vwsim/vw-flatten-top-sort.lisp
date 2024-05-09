; vw-flatten-top-sort.lisp

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

(in-package "ACL2")
(include-book "vw-hrchl-hdl")

;; The next few events are for flattening a heirarchical netlist. All
;; of the modules in the netlist are flattened into one top-level
;; module.

(defun syml-syml-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (car alist)))
      (and (consp entry)
           (symlp (car entry))
           (symlp (cdr entry))
           (syml-syml-alistp (cdr alist))))))

(defun replace-syms (tree alist)
  "Replace instances of symbols in tree with associated symbols in
alist"
  (declare (xargs :guard (syml-syml-alistp alist)))
  (if (atom tree)
      (if (and (assoc tree alist) (not (equal tree nil)))
          (cdr (assoc tree alist))
        tree)
        (cons (replace-syms (car tree) alist)
              (replace-syms (cdr tree) alist))))

(defun rewrite-occs-with-IOs (occs alist)
  (declare (xargs :guard (syml-syml-alistp alist)))
  ;; replace the nodes in each occurrence in
  (if (atom occs)
      nil
    (let ((occ (car occs)))
      (case-match occ
        ((name type nodes . rest)
         (cons (append (list name type (replace-syms nodes alist))
                       rest)
               (rewrite-occs-with-IOs (cdr occs) alist)))
        (& (cw "rewrite-occs-with-IOs: bad occurrence ~p0.~%"
               occ))))))

(in-theory (disable rewrite-occs-with-IOs))

(defun sym-append (sym str)
  (declare (xargs :guard (and (symbolp sym)
                              (stringp str)
                              (standard-char-listp (coerce str 'list)))))
  "Create new symbol appending and inserting a / between the symbol-name and string"
  (if (equal str "")
      sym
    (b* ((new-str (concatenate 'string
                                 (symbol-name sym) "/" (string-upcase str)))
           (new-symbol (intern new-str "ACL2")))
      new-symbol)))

(encapsulate
  ()
  ;; the next few events will go into an encapsulate
  (local
   (defthm car-append
     (implies (and (< 0 (len l1)))
              (equal (car (append l1 l2))
                     (car l1)))))

  (local
   (defthm car-append-str
     (implies (< 0 (len (coerce sym-str 'list)))
              (equal (car (append (coerce sym-str 'list) str2))
                     (car (coerce sym-str 'list))))))

  (local
   (defthm car-sym-append
     (implies (symlp sym)
              (equal (car (coerce (symbol-name (sym-append sym str)) 'list))
                     (car (coerce (symbol-name sym) 'list))))
     :hints
     (("Goal" :in-theory (enable symlp)))))

  (local
   (defthm char-0-car-coerce
     (equal (char str 0) (car (coerce str 'list)))))

  (local
   (defthm char-0-sym-append-coerce
     (implies (symlp sym)
              (equal (char (symbol-name (sym-append sym str)) 0)
                     (char (symbol-name sym) 0)))
     :hints
     (("Goal" :in-theory (disable sym-append)))))

  (local
   (defthm standard-char-p-first-char
     (implies (symlp sym)
              (standard-char-p (char (symbol-name (sym-append sym str)) 0)))
     :hints
     (("Goal" :in-theory (enable symlp)))))

  (local
   (defthm alpha-numeric-p-first-char
     (implies (symlp sym)
              (alpha-numeric-p (char (symbol-name (sym-append sym str)) 0)))
     :hints
     (("Goal" :in-theory (e/d (symlp) (assoc-equal))))))

  (local
   (defthm standard-char-p-char-upcase
     (implies (standard-char-p x)
              (standard-char-p (char-upcase x)))
     :hints
     (("Goal" :in-theory (enable char-upcase)))))

  (local
   (defthm standard-char-listp-string-upcase1
     (implies (standard-char-listp l)
              (standard-char-listp (string-upcase1 l)))
     :hints
     (("Goal" :in-theory (enable standard-char-listp)))))

  (local
   (defthm standard-char-listp-string-upcase
     (implies (and (stringp str)
                   (standard-char-listp (coerce str 'list)))
              (standard-char-listp (coerce (string-upcase str) 'list)))))

  (local
   (defthm standard-char-listp-sym-append
     (implies (and (symlp sym)
                   (stringp str)
                   (standard-char-listp (coerce str 'list)))
              (standard-char-listp (coerce (symbol-name (sym-append sym str)) 'list)))
     :hints
     (("Goal" :in-theory (e/d (symlp standard-char-listp) (string-upcase assoc-equal))))))

  (local
   (defthm car-sym-append-exists
     (implies (symlp sym)
              (consp (coerce (symbol-name (sym-append sym str)) 'list)))
     :rule-classes nil
     :hints
     (("Goal" :in-theory (enable symlp)))))

  (local
   (defthm consp-implies-len>0
     (implies (consp a)
              (< 0 (len a)))
     :rule-classes nil))

  (local
   (defthm len-greater-than-0-sym-append
     (implies (symlp sym)
              (< 0 (len (coerce (symbol-name (sym-append sym str))
                                'list))))
     :hints
     (("Goal"
       :use ((:instance car-sym-append-exists)
             (:instance
              consp-implies-len>0
              (a (coerce (symbol-name (sym-append sym str)) 'list))))))))

  (local
   (defthm member-equal-append
     (iff (member-equal a (append x y))
          (or (member a x)
              (member a y)))))

  (local
   (defthm member-slash-coer
     (member #\/
             (coerce (COERCE (APPEND (COERCE (SYMBOL-NAME SYM) 'LIST)
                                     (CONS #\/
                                           (STRING-UPCASE1 (COERCE STR 'LIST))))
                             'STRING)
                     'list))))

  (local
   (defthm different-slash-implies-not-equal-sym-sym
     (implies (and (symbolp x)
                   (symbolp y)
                   (member-equal #\/ (coerce (symbol-name x) 'list))
                   (not (member-equal #\/ (coerce (symbol-name y) 'list))))
              (equal (equal x y)
                     nil))))

  (local
   (defthm different-slash-implies-not-equal-sym-sym-nil-case
     (let ((x (INTERN-IN-PACKAGE-OF-SYMBOL name 'REWRITE)))
       (implies (and (symbolp x)
                     (member-equal #\/ (coerce (symbol-name x) 'list)))
                x))))

  (local
   (defthm not-booleanp-sym-append
     (implies (symlp sym)
              (not (booleanp (sym-append sym str))))
     :hints
     (("Goal"
       :cases ((equal str ""))
       :in-theory (e/d (symlp booleanp) (assoc-equal))))))

  (in-theory (disable sym-append))

  (defthm symlp-sym-append
    (implies (and (symlp sym)
                  (stringp str)
                  (standard-char-listp (coerce str 'list)))
             (symlp (sym-append sym str)))
    :hints
    (("Goal" :in-theory (e/d (symlp) (char assoc-equal))
      :use ((:instance len-greater-than-0-sym-append)))))
  )

(defun sym-append-list (str list IOs-alist globals)
  "Perform sym-append of str on each element in list if it is not an
  IO or global node"
  (declare (xargs :guard (and (stringp str)
                              (standard-char-listp (coerce str 'list))
                              (syml-listp list)
                              (syml-syml-alistp IOs-alist)
                              (syml-listp globals))))
  (if (atom list)
      nil
    (let* ((sym (car list))
           (IO (assoc-eq sym IOs-alist)))
      (cons (if IO
                (cdr IO)
              (if (member sym globals)
                  (car list)
                (sym-append (car list) str)))
            (sym-append-list str (cdr list) IOs-alist globals)))))

(in-theory (disable sym-append))

(defthm symlp-syml-syml-alistp
  (implies (and (syml-syml-alistp a)
                (assoc-equal k a))
           (symlp (cdr (assoc-equal k a)))))

(defthm syml-listp-sym-append-list
  (implies (and (syml-listp list)
                (stringp str)
                (standard-char-listp (coerce str 'list))
                (syml-syml-alistp IOs-alist))
           (syml-listp (sym-append-list str list IOs-alist globals))))

(in-theory (disable sym-append-list))

(defun measure-fn-flatten (fn-or-occs netlist)
  ;; A measure for flatten-occs
  (declare (xargs :guard t))
  (make-ord (1+ (len netlist))
            1
            (acl2-count fn-or-occs)))

(defthm syml-syml-alistp-pairlis$
  (implies (and (syml-listp l1)
                (syml-listp l2)
                (equal (len l1) (len l2)))
           (syml-syml-alistp (pairlis$ l1 l2))))

(defun flatten-occs (netlist occs IOs-alist parents globals)
  "Flatten a list of occurrences"
  ;; Why is flatten-occs not mutually recursive?  Although the syntax
  ;; may remind the reader of the DUAL-EVAL (de) approach, we simply
  ;; have a heirarchical representation of a graph that can be
  ;; flattened in situ.  The final result is an unordered list of
  ;; primitives and their connections to other primitives; later,
  ;; VWSIM converts these primitives into a matrix using the Modified
  ;; Nodal Approach.
  ;; When a primitive is added to the flattened list, the primitive's
  ;; name, nodes, and branch(es) are modified to indicate the
  ;; heirarchy (chain) of module references that led to this
  ;; primitive. The modifications for the name and branches can be
  ;; summarized as:
  ;; name   -> <module1>/<module2>/.../primitive-name
  ;; branch -> <module1>/<module2>/.../primitive-branch
  ;; If a primitive's node is a module IO node, there is no
  ;; change. Otherwise, the modification is similar to above.
  ;;node -> <module1>/<module2>/.../primitive-node
  (declare (xargs :guard (and (netlist-syntax-okp netlist)
                              (netlist-arity-okp netlist)
                              (occs-syntax-okp occs)
                              (occs-arity-okp occs netlist)
                              (stringp parents)
                              (standard-char-listp (coerce parents 'list))
                              (syml-syml-alistp IOs-alist)
                              (syml-listp globals))
                  :measure    (measure-fn-flatten occs netlist)
                  :verify-guards nil))
  (if (atom occs)
      nil
    (let* ((occ (car occs))
           (occ-name (car occ))
           (occ-type (cadr occ))
           (occ-IOs  (caddr occ)))
      (append
       ;; primitive
       (if (primp occ-type)
           (if (eq occ-type 'k)
               ;; mutual inductance specifies coupling between two inductors
               (list
                (list (sym-append occ-name parents)
                      occ-type
                      ;; the mutual inductance is specified for 2
                      ;; inductors that can be found in the top-level
                      ;; circuit or the same subcircuit.
                      (sym-append-list parents occ-IOs nil nil)
                      ;; the coupling factor
                      (cadddr occ)))

             (let ((occ-brs (cadddr occ))
                   (occ-params (car (cddddr occ))))
               (list
                (list (sym-append occ-name parents)
                      occ-type
                      ;; all nodes get the extension except for the IO
                      ;; nodes and global nodes
                      (sym-append-list parents occ-IOs IOs-alist globals)
                      ;; all branch symbols get the extension
                      (sym-append-list parents occ-brs nil nil)
                      occ-params))))
         ;; module
         (b* ((module (assoc occ-type netlist))
              (module-IOs  (cadr module))
              (module-occs (caddr module))
              (occ-IOs     (sym-append-list parents occ-IOs IOs-alist globals))
              (trans-alist  (pairlis$ module-IOs occ-IOs))

              ;; Prove this away???
              ((unless (syml-syml-alistp trans-alist))
               (cw "flatten-occs: trans-alist is not a syml-syml-alistp.~%~p0~%"
                   trans-alist))

              ;; We check that the occurrences in the module have the
              ;; correct arity with respect to the rest of the modules
              ;; in the netlist. We assume that the netlist has
              ;; already been sorted. Can we prove this check away???
              ((unless (occs-arity-okp module-occs (cdr netlist)))
               (cw "flatten-occs: module-occs fails occs-syntax-okp:~p0.~%"
                   occ))
              )
           (flatten-occs (cdr netlist) module-occs trans-alist
                         (if (equal parents "")
                             (symbol-name occ-name)
                           (concatenate 'string (symbol-name occ-name)
                                        "/" parents))
                         globals)))
       (flatten-occs netlist (cdr occs) IOs-alist parents globals)))))

(defthm standard-char-listp-/
  (implies (standard-char-listp (coerce str 'list))
           (standard-char-listp (cons #\/ (coerce str 'list))))
  :hints
  (("Goal" :in-theory (enable standard-char-listp))))

(verify-guards flatten-occs
  :hints
  (("Goal" :in-theory (e/d (symlp)
                           (assoc-equal true-listp len syml-listp)))))

;; consider other inputs to the function (ex. alist of
;; parameter-values (quote or symbol check), global nodes)
(defun flatten-netlist (netlist globals)
  (declare (xargs :guard (and (netlist-syntax-okp netlist)
                              (netlist-arity-okp netlist)
                              (syml-listp globals))))
  (if (atom netlist)
      nil
    (b* (;; the first module in the netlist is the top-level module
         (module      (car netlist))
         (?module-IOs  (cadr module))
         (module-occs (caddr module))
         ;; no module-IOs for top-level module
         (flat-occs   (flatten-occs (cdr netlist) module-occs nil "" globals)))
      flat-occs)))

#||
;; an example

(flatten-netlist '((top (a b) ((rr1 r (a gnd) (c) ('2))
                               (xw w (a b))))
                   ;; if rr1 and ll1 have the same branch name, do we
                   ;; complain here or after flattening? (in occurrencep)
                   (w   (x y) ((rr1 r (x node) (c) (x))
                               (ll1 l (node gnd) (c) (node)))))
                 '(gnd))

||#

;; Some events for the topological sort of a netlist

(defun topological-sort-occs-okp (occs module-alist)
  "Checks that every occurrence is either a primitive or a key in the
  module-alist"
  (declare (xargs :guard (and (occs-syntax-okp occs)
                              (alistp module-alist))))
  (if (atom occs)
      t
    (let* ((occ (car occs))
           (occ-type (cadr occ)))
      (if (or (primp occ-type)
              (assoc-equal occ-type module-alist))
          (topological-sort-occs-okp (cdr occs) module-alist)
        nil))))

(defun modules-syntax-okp (modules)
  "Recognizes a list of unordered modules"
  (declare (xargs :guard t))
  (if (atom modules)
      (null modules)
    (and (module-syntax-okp (car modules))
         (modules-syntax-okp (cdr modules)))))

(defthm alistp-modules-syntax-okp
  (implies (modules-syntax-okp modules)
           (alistp modules)))

(defthm modules-syntax-okp-remove-assoc-equal
  (implies (modules-syntax-okp netlist)
           (modules-syntax-okp (remove-assoc-equal key netlist))))

(defun topological-sort-help (init-netlist curr-netlist sorted-netlist)
  "Finds modules in init-netlist that can be added to the new sorted
  netlist"
  (declare (xargs :guard (and (modules-syntax-okp init-netlist)
                              (modules-syntax-okp curr-netlist)
                              (modules-syntax-okp sorted-netlist))))
  (if (atom curr-netlist)
      ;; init-netlist is list of modules that have not been sorted. We
      ;; return the remaining unsorted modules to the outer loop.
      (mv init-netlist sorted-netlist)
    (let* ((module (car curr-netlist))
           (module-name (car module))
           (module-occs (caddr module)))
      (if (topological-sort-occs-okp module-occs sorted-netlist)
          (topological-sort-help
           (remove-assoc module-name init-netlist)
           (cdr curr-netlist)
           (cons module sorted-netlist))
        (topological-sort-help init-netlist (cdr curr-netlist) sorted-netlist)))))

(defthm modules-syntax-okp-car-topological-sort-help
  (implies (and (modules-syntax-okp init-netlist)
                (modules-syntax-okp curr-netlist)
                (modules-syntax-okp sorted-netlist))
           (modules-syntax-okp
            (car (topological-sort-help init-netlist
                                        curr-netlist sorted-netlist)))))

(defthm modules-syntax-okp-mv-nth-1-topological-sort-help
  (implies (and (modules-syntax-okp init-netlist)
                (modules-syntax-okp curr-netlist)
                (modules-syntax-okp sorted-netlist))
           (modules-syntax-okp
            (mv-nth 1
                    (topological-sort-help init-netlist
                                           curr-netlist sorted-netlist)))))

(in-theory (disable topological-sort-help))

(defun topological-sort1 (netlist sorted-netlist)
  (declare (xargs :measure (len netlist)
                  :guard (and (modules-syntax-okp netlist)
                              (modules-syntax-okp sorted-netlist))))
  (if (atom netlist)
      sorted-netlist
    (b* (((mv res-netlist res-sorted-netlist)
          (topological-sort-help netlist netlist sorted-netlist))
         ((unless (< (len res-netlist) (len netlist)))
          (cw "topological-sort1: the netlist cannot be topologically
          sorted. Please check for cyclic sub-module references~%. The
          unsorted modules in the netlist: ~%~p0~%. The successfully
          sorted modules in the netlist: ~%~p1~%" netlist
          sorted-netlist)))
      (topological-sort1 res-netlist res-sorted-netlist))))

(defthm modules-syntax-okp-topological-sort1
  (implies (and (modules-syntax-okp netlist)
                (modules-syntax-okp sorted-netlist))
           (modules-syntax-okp (topological-sort1 netlist sorted-netlist))))

(in-theory (disable topological-sort1))

(defun topological-sort (netlist)
  "Performs a topological sort on the netlist produced by
  spice-to-vwsim. This ensures that every occurrence in a module only
  references modules defined later in the netlist"
  (declare (xargs :guard (modules-syntax-okp netlist)))
  (topological-sort1 netlist nil))

(defthm modules-syntax-okp-topological-sort
  (implies (modules-syntax-okp netlist)
           (modules-syntax-okp (topological-sort netlist))))

(in-theory (disable topological-sort))

#||
(!! flatten-example-1
    '((M1
       ()
       ((XM2 M2 (A))))
      (M2
       (B)
       ((RR1 R (A B) (i-rr1) ('1))))))

;; (flatten-netlist (@ flatten-example-1) nil)

(!! flatten-example-2
    '((M1
       ()
       ((XM2 M2 (A GND))))
      (M2
       (B C)
       ((RR1 R (A B) (i-rr1) ('1))
        (CC1 C (B C) (i-cc1) ('1))
        (XM3 ))))
||#

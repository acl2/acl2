; Fixtypes for fixed-length lists of unsigned 8-bit bytes -- Macro
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
; Alessandro Coglio (coglio@kestrel.edu)
; and Eric McCarthy (last name at same site).

; This file is based on defbyte.lisp,
; modified to define fixed-length lists of 8-bit bytes.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "kestrel/utilities/event-forms" :dir :system)

(include-book "defbyte")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Usage:
;;
;;   (defbytelistoflen 'B 32)
;;
;; defines the fixtype B32, including:
;;
;; * The predicate B32p, which tests if the argument is a
;;   "list of exactly 32 unsigned 8-bit bytes" (represented as a list)
;; * The fixing function B32-fix
;; * The fixtype B32
;; * related theorems (suggestions welcome)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Preliminaries.

;; Using defbyte,
;; define predicates, fixing functions, and fixtypes for unsigned 8-bit bytes
;; and lists of unsigned 8-bit bytes, for use by defbytelistoflen.

;; Predicates:
;;   ubyte8p
;;   ubyte8-listp
;; Fixing functions:
;;   ubyte8-fix
;;   ubyte8-list-fix
;; Fixtypes:
;;   ubyte8
;;   ubyte8-list
;; Also defines related theorems.

;; This will be redundant if fixbytes/instances.lisp
;; has been loaded, but if not, we need it here.

(defbyte 8 :unsigned)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defsection defbytelistoflen
  :parents (kestrel-utilities fty::fty)
  :short "Introduce <see topic='@(url fty)'>fixtype</see> for
          fixed-length true lists of unsigned 8-bit bytes."
  :long
  "<p>
   Currently, @(tsee defbyte) can be used to define fixtypes
   for unsigned or signed bytes of specified sizes, as well
   as for true lists thereof.  @('defbytelistoflen') defines a fixtype
   that also constrains the length of the list to be fixed,
   but only supports unsigned 8-bit bytes.
   </p>
   <p>
   This macro introduces unary predicates and associated fixtypes
   for fixed-length lists of unsigned 8-bit bytes.
   It also generates theorems that relate the defined predicates
   to other predicates.
   The arguments to the macro are (1) a symbol used as a prefix for
   the fixtype name, represented by @('<basename>') below, and
   (2) a positive integer @('<n>') that is appended to the
   name prefix that specifies the length of the list.
   </p>
   <p>
   More precisely, this macro generates:
   </p>
   <ul>
     <li>
     A unary predicate for fixed-length true lists of length
     @('<n>') of unsigned 8-bit bytes.  The generated name is
     @('<basename><n>p').  By default, the rewrite rule for the
     predicate is disabled.
     </li>
     <li>
     A fixing function.  This fixing function is for use in a
     logical context. Its parameter has a guard and when executed it is
     simply the identify function for efficiency.  If you need an
     \"executable\" fixing function that takes any argument and returns
     a value to satisfy the predicate, see @('<basename><n>-fix-pad') below,
     or write your own function.  The generated name
     is @('<basename><n>-fix').
     </li>
     <li>
     A padding fixing function.  This fixing function is for use when
     you want to actually perform fixing in an execution context.
     The function, if passed a list of unsigned 8-bit bytes that has length
     less than @('<n>'), left-pads the list with zeros to make it have length
     @('<n>').  Otherwise, if the argument does not satisfy the
     predicate, this function returns the zero constant (see below).
     The generated name is @('<basename><n>-fix-pad').
     </li>
     <li>
     A zero constant---a list of @('<n>') zeros to use as the executable fixing
     function target when the predicate fails.
     The generated name is @('*<basename><n>-zeros*').
     </li>
     <li>
     A <see topic='@(url fty)'>fixtype</see> for fixed-length true lists of length
     @('<n>') of unsigned 8-bit bytes.  The generated name is @('<basename><n>').
     </li>
     <li>
     A rule showing that when the predicate is true, the fixing function
     is the identity function.
     </li>
   </ul>
   <p>
   These generated items include XDOC documentation.
   </p>
   @(def defbytelistoflen)"

  (define defbytelistoflen-fn ((basename symbolp) (n posp))
    :returns (event pseudo-event-formp
                    ;; just to speed up the proof:
                    :hints (("Goal" :in-theory (disable packn))))
    :verify-guards nil
    (b* (
         (bytes<n> (packn (list basename n)))
         (bytes<n>p (packn (list basename n 'p)))
         (bytes<n>-zeros (packn (list '* bytes<n> '-zeros*)))
         (bytes<n>-fix-pad (packn (list basename n '-fix-pad)))
         (bytes<n>-fix (packn (list basename n '-fix)))
         (bytes<n>-equiv (packn (list basename n '-equiv)))
         (bytes<n>-fix-when-bytes<n>p (packn (list bytes<n>-fix '-when- bytes<n>p)))
         ;; This is used for the doc strings:
         (<n>string (coerce (explode-nonnegative-integer n 10 nil) 'string))
         )
      `(progn
         (define ,bytes<n>p (x)
           :returns (yes/no booleanp)
           :parents (defbytelistoflen)
           :short ,(concatenate 'string
                                "Recognize list of exactly "
                                <n>string
                                " unsigned"
                                " 8-bit"
                                " bytes"
                                ".")
           (and (ubyte8-listp x)
                (equal (len x) ,n)))
         (defsection ,bytes<n>-zeros
           :parents (defbytelistoflen)
           :short ,(concatenate 'string
                                "Constant list of " <n>string " zeros.")
           (defconst ,bytes<n>-zeros (repeat ,n 0)))
         (define ,bytes<n>-fix-pad (x)
           :returns (fixed-x ,bytes<n>p :hints (("Goal" :in-theory (enable ,bytes<n>p))))
           :parents (defbytelistoflen)
           :short ,(concatenate 'string
                                "Executable padding fixing function for @(tsee "
                                (symbol-name bytes<n>p)
                                "). If passed a shorter list, left-pads the "
                                "list with zeros.")
           (if (,bytes<n>p x)
               x
             (if (and (ubyte8-listp x)
                      (< (len x) ,n))
                 (append (repeat (- ,n (len x)) 0)
                         x)
               ,bytes<n>-zeros)))
         (define ,bytes<n>-fix ((x ,bytes<n>p))
           :returns (fixed-x ,bytes<n>p)
           :parents (defbytelistoflen)
           :short ,(concatenate 'string
                                "Logical fixing function for @(tsee "
                                (symbol-name bytes<n>p)
                                ").")
           :guard-hints (("Goal" :in-theory (enable ,bytes<n>-fix-pad)))
           (mbe :logic (,bytes<n>-fix-pad x)
                :exec x)
           :no-function t
           ///
           (defrule ,bytes<n>-fix-when-bytes<n>p
             (implies (,bytes<n>p x)
                      (equal (,bytes<n>-fix x) x))
             :enable (,bytes<n>p ,bytes<n>-fix-pad)))
         (defsection ,bytes<n>
           :parents (defbytelistoflen)
           :short ,(concatenate 'string
                                "<see topic='@(url fty)'>Fixtype</see> for"
                                " lists of "
                                <n>string
                                " unsigned"
                                " 8-bit"
                                " bytes"
                                ".")
           (fty::deffixtype ,bytes<n>
             :pred ,bytes<n>p
             :fix ,bytes<n>-fix
             :equiv ,bytes<n>-equiv
             :define t
             :forward t))
         )))

  (defmacro defbytelistoflen (basename n)
    (declare (xargs :guard (and (posp n) (symbolp basename))))
    `(make-event (defbytelistoflen-fn ',basename ,n))))

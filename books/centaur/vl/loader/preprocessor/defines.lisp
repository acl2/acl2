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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../../util/defs")
(include-book "../../util/echars")
(include-book "../../util/warnings")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(local (xdoc::set-default-parents vl-define))

(fty::defprod vl-define-formal
  :short "A formal argument to a @('`define') directive."
  ((name    stringp
            :rule-classes :type-prescription
            "Name of the formal argument.  This should be a simple
             identifier.")
   (default maybe-stringp
            :rule-classes :type-prescription
            "SystemVerilog only: default text for the argument, if applicable,
             or NIL if no default was provided.  Note that we generally expect
             this to be trimmed of any whitespace.")))

(fty::deflist vl-define-formallist
  :elt-type vl-define-formal)

(defprojection vl-define-formallist->names ((x vl-define-formallist-p))
  :returns (names string-listp)
  (vl-define-formal->name x))

(fty::defprod vl-define
  :parents (preprocessor)
  :short "Internal representation of a @('`define') directive."
  ((name    stringp :rule-classes :type-prescription)
   (formals vl-define-formallist-p
            "Formal arguments to the text macro, if any.")
   (body    stringp :rule-classes :type-prescription
            "Macro text associated with this definition. Note that we generally
             expect this to be trimmed of any whitespace.")
   (loc     vl-location-p
            "Location of this definition in the source code.")
   (stickyp booleanp :rule-classes :type-prescription
            "Is this define \"sticky\".  If so, and we encounter another
             @('`define') of @('name'), then we keep the old definition instead
             of redefining it.  This is similar to how other tools
             treat command-line @('+define') options; see the @('defines')
             cosim for more details.")))

(fty::deflist vl-defines
  :parents (preprocessor)
  :elt-type vl-define)

(defprojection vl-defines->names ((x vl-defines-p))
  :returns (names string-listp)
  (vl-define->name x))

(define vl-find-define
  :short "Look up a definition in the defines list."
  ((name stringp)
   (x    vl-defines-p))
  :returns (guts (iff (vl-define-p guts) guts))
  (cond ((atom x)
         nil)
        ((equal (string-fix name) (vl-define->name (car x)))
         (vl-define-fix (car x)))
        (t
         (vl-find-define name (cdr x)))))

(define vl-delete-define
  :short "Delete an entry from the defines list, if it exists."
  ((name stringp)
   (x    vl-defines-p))
  :returns (new-x vl-defines-p)
  (cond ((atom x)
         nil)
        ((equal (string-fix name) (vl-define->name (car x)))
         (vl-delete-define name (cdr x)))
        (t
         (cons (vl-define-fix (car x))
               (vl-delete-define name (cdr x))))))

(define vl-add-define
  :short "Add a definition to the defines list."
  ((a vl-define-p)
   (x vl-defines-p))
  :returns (new-x vl-defines-p)
  (cons (vl-define-fix a) (vl-defines-fix x)))

(define vl-make-initial-defines ((x string-listp)
                                 &key (stickyp booleanp))
  :returns (defs vl-defines-p)
  :short "Simple way to build a @(see vl-defines-p) that @('`define')s a list
of names to @('1')."
  (if (atom x)
      nil
    (cons (make-vl-define :name (car x)
                          :formals nil
                          :body "1"
                          :loc *vl-fakeloc*
                          :stickyp stickyp)
          (vl-make-initial-defines (cdr x) :stickyp stickyp))))


(local (defthm position-type
         ;; Ugh -- why isn't this built in?
         (or (not (position-equal x l))
             (natp (position-equal x l)))
         :rule-classes :type-prescription
         :hints(("Goal" :in-theory (enable position-equal)))))

(define vl-parse-cmdline-define ((x stringp)
                                 (loc vl-location-p)
                                 (stickyp booleanp))
  :returns (mv (okp booleanp :rule-classes :type-prescription)
               (def (iff (vl-define-p def) okp)))
  :short "Essentially treats @('\"foo\") like @('`define foo'), or
@('\"foo=3\"') like @('`define foo 3`')."
  :long "<p>BOZO we could do better sanity checking here.</p>"
  (b* ((x (string-fix x))
       (pos (position #\= x))
       ((unless pos)
        (mv t (make-vl-define :name x
                              :formals nil
                              :body ""
                              :loc loc
                              :stickyp stickyp)))
       ((unless (< (+ 1 pos) (length x)))
        (mv nil nil))
       (name (subseq x 0 pos))
       (body (subseq x (+ 1 pos) nil)))
    (mv t (make-vl-define :name name
                          :formals nil
                          :body body
                          :loc loc
                          :stickyp stickyp))))

;(vl-parse-cmdline-define "foo" *vl-fakeloc* nil)
;(vl-parse-cmdline-define "foo=" *vl-fakeloc* nil)
;(vl-parse-cmdline-define "foo=bar" *vl-fakeloc* nil)

(define vl-parse-cmdline-defines-aux ((x string-listp)
                                      (loc vl-location-p)
                                      (stickyp booleanp))
  :returns (mv (warnings vl-warninglist-p)
               (defs vl-defines-p))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv okp first)
        (vl-parse-cmdline-define (car x) loc stickyp))
       ((mv warnings rest)
        (vl-parse-cmdline-defines-aux (cdr x) loc stickyp))
       ((when okp)
        (mv warnings (cons first rest))))
    (mv (fatal :type :vl-bad-define
               :msg "Error parsing command-line define: ~s0"
               :args (list (string-fix (car x))))
        rest)))

(define vl-parse-cmdline-defines ((x      string-listp)
                                  (loc    vl-location-p)
                                  (sticky booleanp))
  :returns (mv (warnings vl-warninglist-p)
               (defs     vl-defines-p))
  (b* (((mv warnings defs)
        (vl-parse-cmdline-defines-aux x loc sticky))
       (dupes (duplicated-members
               (vl-defines->names
                ;; Sort first to remove true redundancies
                (set::mergesort defs))))
       (warnings (if (not dupes)
                     (ok)
                   (fatal :type :vl-bad-defines
                          :msg "Conflict command-line defines for ~&0."
                          :args (list dupes)))))
    (mv warnings defs)))

;; (vl-parse-cmdline-defines (list "foo" "bar" "baz=3" "baz=5")
;;                           *vl-fakeloc* t)



(defprod vl-ifdef-context
  :parents (preprocessor)
  :short "Information about a single use of @('ifdef FOO') or @('elsif BAR')."
  :layout :tree
  :tag nil
  ((loc     vl-location-p "Location where the @('`ifdef FOO') or @('elsif BAR') occurred.")
   ;; maybe eventually other things
   ))

(fty::deflist vl-ifdef-context-list
  :elt-type vl-ifdef-context
  :parents (preprocessor))

(fty::defalist vl-ifdef-use-map
  :parents (preprocessor)
  :key-type stringp
  :val-type vl-ifdef-context-list
  :keyp-of-nil nil
  :valp-of-nil t
  :short "A log of where @('`define')s are used in the @('`ifdef') tree.")

(define vl-extend-ifdef-map ((name stringp)
                             (ctx  vl-ifdef-context-p)
                             (map  vl-ifdef-use-map-p))
  :parents (vl-ifdef-use-map)
  :returns (new-map vl-ifdef-use-map-p)
  (b* ((name (string-fix name))
       (ctx  (vl-ifdef-context-fix ctx))
       (map  (vl-ifdef-use-map-fix map))
       (prev-uses (cdr (hons-get name map)))
       (new-uses  (cons ctx prev-uses)))
    (hons-acons name new-uses map)))



(defprod vl-def-context
  :parents (preprocessor)
  :short "Information about a single use of a define like @('`FOO')."
  :layout :tree
  :tag nil
  ((activep booleanp      "Was this use in code that was actively being preprocessed?")
   (loc     vl-location-p "Location where the use of @('`FOO') occurred.")))

(fty::deflist vl-def-context-list
  :elt-type vl-def-context
  :parents (preprocessor))

(fty::defalist vl-def-use-map
  :parents (preprocessor)
  :key-type stringp
  :val-type vl-def-context-list
  :keyp-of-nil nil
  :valp-of-nil t
  :short "A log of where @('`define')s are used, outside of ifdefs.")

(define vl-extend-def-map ((name stringp)
                           (ctx  vl-def-context-p)
                           (map  vl-def-use-map-p))
  :parents (vl-def-use-map)
  :returns (new-map vl-def-use-map-p)
  (b* ((name      (string-fix name))
       (ctx       (vl-def-context-fix ctx))
       (map       (vl-def-use-map-fix map))
       (prev-uses (cdr (hons-get name map)))
       (new-uses  (cons ctx prev-uses)))
    (hons-acons name new-uses map)))



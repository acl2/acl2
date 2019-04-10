; ACL2 Standard Library
; Copyright (C) 2008-2016 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "STOBJS")
(include-book "std/util/bstar" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "tools/templates" :dir :system)
(program)

(defxdoc defstobj-clone
  :parents (std/stobjs)
  :short "Create a new stobj that is @(':congruent-to') an existing (concrete
or abstract) stobj, and can be given to functions that operate on the old
stobj."

  :long "<p>@('Defstobj-clone') lets you easily introduce a new @(see stobj)
that is @(':congruent-to') an existing stobj.  This allows you to have two (or
more) copies of a stobj that coexist simultaneously.</p>

<h3>Basic Example</h3>

<p>If you want to write an algorithm that operates on two bit arrays, you might
clone the @(see bitarr) to get a second stobj, @('bitarr2').  A minimal way to
do this is:</p>

@({
    (defstobj-clone bitarr2 bitarr :suffix \"2\")
})

<p>This introduces:</p>

<ul>

<li>A new stobj, @('bitarr2'), which is congruent to @('bitarr'), and</li>

<li>New functions that are basically renamed @('bitarr') operations.  In
particular, whereas @('bitarr') has operations like @('get-bit') and
@('set-bit'), we'll get new functions named @('get-bit2') and
@('set-bit2').</li>

</ul>

<p>Usually you can just <b>ignore</b> these new functions.  They are added only
because of the way that ACL2 stobj definition works and, strictly speaking, are
not really necessary for anything else because you can still use the original
stobj's functions on the new stobj.</p>

<p>Ignoring the new functions is particularly useful when you have already
built up more complex functionality on top of a stobj.  That is, if you've
implemented functions like @('clear-range') and @('invert-range') or similar,
you can just use these on @('bitarr2') without reimplementing them.</p>


<h3>Renaming Accessors</h3>

<p>On the other hand, it may occasionally be useful for code clarity to rename
the new functions in some semantically meaningful way.  For instance, if your
cloned bit array will be used as a seen table, it may be convenient to use
operations like ('set-seen') instead of @('set-bit').</p>

<p>To support using such semantically meaningful names, @('defstobj-clone') has
a variety of options.  Here is a contrived example that uses all of them:</p>

@({
    (defstobj-clone fancy-bitarr bitarr
      :strsubst ((\"GET\" . \"FETCH\")     ;; Substring replacements to make
                 (\"SET\" . \"INSTALL\"))  ;;   (capitalized per symbol names)
      :prefix \"MY-\"                      ;; Name prefix to add
      :suffix \"-FOR-JUSTICE\"             ;; Name suffix to add
      :pkg acl2::rewrite                   ;; Package for new symbols
                                           ;;   default: new stobj name
      )
})

<p>The result is to define new analogues of the @('bitarr') functions with the
following names:</p>

@({
      bitarrp       -->  fancy-bitarrp
      create-bitarr -->  create-fancy-bitarr
      bits-length   -->  my-bits-length-for-justice
      get-bit       -->  my-fetch-bit-for-justice
      set-bit       -->  my-install-bit-for-justice
      resize-bits   -->  my-resize-bits-for-justice
})


<h3>Alternate Syntax for Abstract Stobjs</h3>

<p>For an abstract stobj, the accessors/updaters are known as \"exports\".
Another way to specifying their names in the new stobj is to provide the
@(':exports') argument, which should be a list of symbols corresponding to the
exported functions from the original abstract stobj.  When this is provided,
the other keyword arguments are unused.  For example:</p>

@({
    (defstobj-clone xx-bitarr bitarr
      :exports (xx-size xx-nth !xx-nth xx-resize))
})

<p>Defines a new @('xx-bitarr') stobj with:</p>

@({
    bitarrp       --> xx-bitarrp
    create-bitarr --> create-xx-bitarr
    bits-length   --> xx-size
    get-bit       --> xx-nth
    set-bit       --> !xx-nth
    resize-bits   --> xx-resize
})")


(defun clone-stobj-change-symbol (sym renaming)
  (if renaming
      (b* (((list prefix suffix strsubst pkg) renaming)
           ((mv sub pkg?) (acl2::tmpl-str-sublis strsubst (symbol-name sym))))
        (intern-in-package-of-symbol
         (concatenate 'string prefix sub suffix)
         (or pkg? pkg)))
    sym))

(defun clone-stobj-process-rename-alist (rename-alist renaming)
  (if (atom rename-alist)
      nil
    (cons (list (clone-stobj-change-symbol (caar rename-alist) renaming)
                (clone-stobj-change-symbol (cadar rename-alist) renaming))
          (clone-stobj-process-rename-alist (cdr rename-alist) renaming))))

(defun clone-stobj-process-fields (fields renaming)
  (if (atom fields)
      nil
    (cons (if (consp (car fields))
              (cons (clone-stobj-change-symbol (caar fields) renaming)
                    (cdar fields))
            (clone-stobj-change-symbol (car fields) renaming))
          (clone-stobj-process-fields (cdr fields) renaming))))




(defun keep-nonbool-symbols (x)
  (if (atom x)
      nil
    (let* ((k (car x)))
      (if (and k (not (eq k t)) (symbolp k))
          (cons k (keep-nonbool-symbols (cdr x)))
        (keep-nonbool-symbols (cdr x))))))

;; each field is: (fieldp type initial-val others)
;; and others are all either function names, NIL when the functions aren't
;; applicable, and a resizable flag (boolean).
(defun stobj-field-template-fnnames (field-templates)
  (if (atom field-templates)
      nil
    (cons (caar field-templates)
          (append
           (keep-nonbool-symbols (cdddar field-templates))
           (stobj-field-template-fnnames (cdr field-templates))))))

(defun stobj-template-fnnames (template)
  (list* (car template)  ;; stobjp
         (cadr template) ;; create-stobj
         ;; field fns
         (stobj-field-template-fnnames (caddr template))))


(defun clone-stobj-process-args (stobjname args renaming)
  (b* (((mv erp field-descriptors key-alist)
        (acl2::partition-rest-and-keyword-args args acl2::*defstobj-keywords*))
       ((when erp)
        (er hard? 'defstobj-clone
            "The stobj to be cloned had bad keyword args~%"))
       (inline (assoc-eq :inline key-alist))
       (fields (clone-stobj-process-fields field-descriptors renaming)))
    (append fields
            (and inline (list :inline (cdr inline)))
            (list
; Matt K. mod: :doc is no longer supported for defstobj after v7-1
             ;; :doc
             ;; (concatenate 'string "Clone of stobj "
             ;; (symbol-name stobjname))
             :congruent-to stobjname))))

(defun clone-stobj-rewrite (newfn oldfn formals)
  (let ((thmname (intern-in-package-of-symbol
                    (concatenate 'string (symbol-name newfn) "-IS-" (symbol-name oldfn))
                    newfn)))
    `((defthm ,thmname
        (equal (,newfn . ,formals)
               (,oldfn . ,formals))
        :hints (("goal" :in-theory '(,newfn ,oldfn))
                (and stable-under-simplificationp
                     '(:in-theory (e/d** (clone-stobj-tmp-rules))))
                (and stable-under-simplificationp
                     '(:in-theory '(,newfn ,oldfn (:induction ,newfn))))))
      (local (add-to-ruleset! clone-stobj-tmp-rules ,thmname)))))

;; new and old are the lists of axiomatic defs
(defun clone-stobj-rewrites (new old)
  (b* (((when (atom new)) nil)
       (newfn (caar new))
       (formals (cadar new))
       (oldfn (caar old)))
    (append (clone-stobj-rewrite newfn oldfn formals)
            (clone-stobj-rewrites (cdr new) (cdr old)))))





(defun clone-base-stobj-fn (stobjname name renaming wrld)
  (b* ((ev-wrld (acl2::decode-logical-name stobjname wrld))
       ((when (null ev-wrld))
        (er hard? 'defstobj-clone
            "Unrecognized stobjname: ~x0~%" stobjname))
       (event (acl2::access-event-tuple-form (cddar ev-wrld)))
       ((when (not (eq (car event) 'acl2::defstobj)))
        (er hard? 'defstobj-clone
            "The event named ~x0 is not a defstobj event~%" stobjname))
       ((list* & ;; defstobj
               & ;; stobjname
               args) event)
       (name (or name (clone-stobj-change-symbol stobjname renaming)))
       (new-args (clone-stobj-process-args stobjname args renaming))
       (old-template (acl2::defstobj-template stobjname args wrld))
       (new-template (acl2::defstobj-template name new-args wrld))
       (old-defs (acl2::defstobj-axiomatic-defs stobjname old-template wrld))
       (new-defs (acl2::defstobj-axiomatic-defs name new-template wrld)))
    (list* 'encapsulate nil `(defstobj ,name . ,new-args)
           '(local (def-ruleset! clone-stobj-tmp-rules nil))
           (clone-stobj-rewrites new-defs old-defs))))

(defun clone-absstobj-exports (exports logic-exec renaming concrete world)
  (b* (((when (atom exports)) nil)
       ((cons logic exec) (car logic-exec))
       (new-sym (clone-stobj-change-symbol (car exports) renaming))
       (protect (acl2::unprotected-export-p concrete exec world)))
    (cons `(,new-sym :logic ,logic :exec ,exec :protect ,protect)
          (clone-absstobj-exports
           (cdr exports) (cdr logic-exec) renaming concrete world))))

(defun clone-absstobj-fn (stobjname name renaming user-exports world)
  (b* ((abs-info (fgetprop stobjname 'acl2::absstobj-info nil world))
       (stobj-info (fgetprop stobjname 'acl2::stobj nil world))
       (`(,concrete
          (,recog-logic . ,recog-exec)
          (,create-logic . ,create-exec)
          . ,export-logic-exec)
        abs-info)
       (`(,& ,?pred ,?create . ,exports) stobj-info)
       (exports (or user-exports exports))
       (creator (acl2::defstobj-fnname name :creator :top nil))
       (recognizer (acl2::defstobj-fnname name :recognizer :top nil)))
    `(defabsstobj ,name
       :concrete ,concrete
       :recognizer (,recognizer :logic ,recog-logic :exec ,recog-exec)
       :creator (,creator :logic ,create-logic :exec ,create-exec)
       :exports ,(clone-absstobj-exports exports export-logic-exec renaming
                                         ;; needed for computing :protect args
                                         concrete world)
       :congruent-to ,stobjname)))



(defun clone-stobj-fn (stobjname name prefix suffix strsubst pkg exports world)
  (declare (xargs :guard (and (stringp prefix)
                              (stringp suffix)
                              (alistp strsubst)
                              (string-listp (strip-cars strsubst))
                              (string-listp (strip-cdrs strsubst))
                              (symbol-listp exports)
                              (symbolp pkg)
                              (not (and (equal prefix "")
                                        (equal suffix "")
                                        (not strsubst)
                                        (not exports)
                                        (not pkg)))
                              )))
  (b* ((stobjp (fgetprop stobjname 'acl2::stobj nil world))
       (absstobjp (fgetprop stobjname 'acl2::absstobj-info nil world))
       (pkg (or pkg name))
       ;; don't rename if exports are provided
       (renaming (and (not exports)
                      (list prefix suffix strsubst pkg)))
       ((unless stobjp)
        (er hard? 'defstobj-clone
            "~x0 is not a stobj~%" stobjname)))
    (if absstobjp
        (clone-absstobj-fn stobjname name renaming exports world)
      (if exports
          (er hard? 'defstobj-clone
              ":Exports is not supported for concrete stobjs")
        (clone-base-stobj-fn stobjname name renaming world)))))



(defmacro defstobj-clone (newname origname &key
                                  strsubst
                                  (prefix '"")
                                  (suffix '"")
                                  pkg
                                  exports)
  `(make-event (clone-stobj-fn ',origname ',newname ',prefix ',suffix
                               ',strsubst ',pkg ',exports (w state))))



; Tool for defining stobj/absstobjs congruent to existing ones
; Copyright (C) 2013 Centaur Technology
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

(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "rulesets")
(include-book "templates")

(program)

(defun clone-stobj-change-symbol (sym renaming)
  (if renaming
      (b* (((list prefix suffix strsubst pkg) renaming)
           ((mv sub pkg?) (tmpl-str-sublis strsubst (symbol-name sym))))
        (intern-in-package-of-symbol
         (concatenate 'string prefix sub suffix)
         (or pkg? pkg)))
    sym))

(defun clone-stobj-process-rename-alist (rename-alist renaming)
  (if (atom rename-alist)
      nil
    (cons (cons (clone-stobj-change-symbol (caar rename-alist) renaming)
                (clone-stobj-change-symbol (cdar rename-alist) renaming))
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
        (partition-rest-and-keyword-args args *defstobj-keywords*))
       ((when erp)
        (er hard? 'defstobj-clone
            "The stobj to be cloned had bad keyword args~%"))
       (rename-alist (cdr (assoc-eq :renaming key-alist)))
       (new-renaming (clone-stobj-process-rename-alist rename-alist renaming))
       (inline (assoc-eq :inline key-alist))
       (fields (clone-stobj-process-fields field-descriptors renaming)))
    (append fields
            (and renaming (list :renaming new-renaming))
            (and inline (list :inline (cdr inline)))
            (list :doc
                  (concatenate 'string "Clone of stobj "
                               (symbol-name stobjname))
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
  (b* ((ev-wrld (decode-logical-name stobjname wrld))
       ((when (null ev-wrld))
        (er hard? 'defstobj-clone
            "Unrecognized stobjname: ~x0~%" stobjname))
       (event (access-event-tuple-form (cddar ev-wrld)))
       ((when (not (eq (car event) 'defstobj)))
        (er hard? 'defstobj-clone
            "The event named ~x0 is not a defstobj event~%" stobjname))
       ((list* & ;; defstobj
               & ;; stobjname
               args) event)
       (name (or name (clone-stobj-change-symbol stobjname renaming)))
       (new-args (clone-stobj-process-args stobjname args renaming))
       (old-template (defstobj-template stobjname args wrld))
       (new-template (defstobj-template name new-args wrld))
       (old-defs (defstobj-axiomatic-defs stobjname old-template wrld))
       (new-defs (defstobj-axiomatic-defs name new-template wrld)))
    (list* 'encapsulate nil `(defstobj ,name . ,new-args)
           '(local (def-ruleset! clone-stobj-tmp-rules nil))
           (clone-stobj-rewrites new-defs old-defs))))

(defun clone-absstobj-exports (exports logic-exec renaming concrete world)
  (b* (((when (atom exports)) nil)
       ((cons logic exec) (car logic-exec))
       (new-sym (clone-stobj-change-symbol (car exports) renaming))
       (protect (unprotected-export-p concrete exec world)))
    (cons `(,new-sym :logic ,logic :exec ,exec :protect ,protect)
          (clone-absstobj-exports
           (cdr exports) (cdr logic-exec) renaming concrete world))))

(defun clone-absstobj-fn (stobjname name renaming user-exports world)
  (b* ((abs-info (fgetprop stobjname 'absstobj-info nil world))
       (stobj-info (fgetprop stobjname 'stobj nil world))
       (`(,concrete
          (,recog-logic . ,recog-exec)
          (,create-logic . ,create-exec)
          . ,export-logic-exec)
        abs-info)
       (`(,& ,?pred ,?create . ,exports) stobj-info)
       (exports (or user-exports exports))
       (creator (defstobj-fnname name :creator :top nil))
       (recognizer (defstobj-fnname name :recognizer :top nil)))
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
                              (not (and (equal prefix "")
                                        (equal suffix "")
                                        (not strsubst)
                                        (not exports))))))
  (b* ((stobjp (fgetprop stobjname 'stobj nil world))
       (absstobjp (fgetprop stobjname 'absstobj-info nil world))
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


(defxdoc defstobj-clone
  :parents (stobjs)
  :short "Create a new stobj that is congruent to an existing (concrete or
abstract) stobj"
  :long "
<h2>Usage:</h2>
@({
 (defstobj-clone new-stobj orig-stobj
         :strsubst ((\"OLDSTR\" . \"NEWSTR\")
                    (\"ETC\"    . \"ANDSOON\"))
         :prefix \"NEW\"
         :suffix \"++\"
         :pkg mypkg::some-symbol
         ;; Only supported for abstract stobjs
         :exports (new-get new-set new-acc new-upd))
})

<p>This defines a new stobj called @('NEW-STOBJ') that is congruent to the
existing stobj @('ORIG-STOBJ').  The keyword arguments all have to do with the
way the fields and accessor/updater functions of stobjs are renamed (they must
be given new names in the new stobj).</p>

<p>For an abstract stobj, the accessors/updaters are known as \"exports\".  One
option for specifying their names in the new stobj is to provide the
@(':exports') argument, which should be a list of symbols corresponding to the
exported functions from the original abstract stobj.  When this is provided,
the other keyword arguments are unused.</p>

<p>If @(':exports') is not used (which it can't be in cloning a concrete
stobj), then one or more of @(':strsubst'), @(':prefix'), and @(':suffix') must
be given.  Prefix and suffix should be strings, and strsubst should be an alist
with string keys and values.  The @(':pkg') symbol is optional and determines
into what package new symbols are interned; by default, it is the package of
the new stobj name.</p>")

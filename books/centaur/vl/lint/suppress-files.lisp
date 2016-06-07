; VL Lint - Whole-File Warning Suppression
; Copyright (C) 2016 Apple, Inc.
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

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defsection lint-whole-file-suppression
  :parents (vl-lint warnings)
  :short "A filter for dropping warnings from whole modules (and other
design elements) based on filenames.")

(local (xdoc::set-default-parents lint-whole-file-suppression))

(define vl-filename-to-suppress-p-aux
  ((filename          stringp "File where some warnings occur.")
   (suppress-filename stringp "Files the user wants to suppress."))
  :returns (suppress-p booleanp :rule-classes :type-prescription)
  (b* ((filename (string-fix filename))
       (suppress-filename (string-fix suppress-filename))
       ((when (str::strprefixp "/" suppress-filename))
        ;; User wants to suppress an absolute path, require full equality, I
        ;; guess.  Hrmn, this might not be great, we might want to instead do
        ;; something like normalizing both paths, but OSLIB is so barren...
        (equal filename suppress-filename)))
    (str::strsuffixp suppress-filename filename)))

(define vl-filename-to-suppress-p ((filename stringp)
                                   (suppress-files string-listp))
  :returns (suppress-p booleanp :rule-classes :type-prescription)
  (if (atom suppress-files)
      nil
    (or (vl-filename-to-suppress-p-aux filename (car suppress-files))
        (vl-filename-to-suppress-p filename (cdr suppress-files)))))


(defmacro def-vl-suppress-file-warnings (name)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (elem-fn        (mksym 'vl- name '-suppress-file-warnings))
       (list-fn        (mksym 'vl- name 'list-suppress-file-warnings))
       (elem-p         (mksym 'vl- name '-p))
       (elem-fix       (mksym 'vl- name '-fix))
       (list-p         (mksym 'vl- name 'list-p))
       (elem->loc      (mksym 'vl- name '->minloc))
       (elem->warnings (mksym 'vl- name '->warnings))
       (change-elem    (mksym 'change-vl- name)))
    `(progn
       (define ,elem-fn ((x ,elem-p)
                         (suppress-files string-listp))
         :returns (new-x ,elem-p)
         (if (and
              ;; Dumb optimization: don't do string comparisons unless
              ;; there are actually warnings to suppress.
              (consp (,elem->warnings x))
              (vl-filename-to-suppress-p (vl-location->filename (,elem->loc x))
                                         suppress-files))
             (,change-elem x :warnings nil)
           (,elem-fix x)))

       (defprojection ,list-fn ((x ,list-p)
                                (suppress-files string-listp))
         :returns (new-x ,list-p)
         (,elem-fn x suppress-files)))))

(def-vl-suppress-file-warnings module)
(def-vl-suppress-file-warnings udp)
(def-vl-suppress-file-warnings interface)
(def-vl-suppress-file-warnings program)
(def-vl-suppress-file-warnings class)
(def-vl-suppress-file-warnings package)
(def-vl-suppress-file-warnings config)

(define vl-design-suppress-file-warnings ((x vl-design-p)
                                          (files string-listp))
  :returns (new-x vl-design-p)
  (b* (((vl-design x)))
    (change-vl-design
     x
     :mods       (vl-modulelist-suppress-file-warnings    x.mods       files)
     :udps       (vl-udplist-suppress-file-warnings       x.udps       files)
     :interfaces (vl-interfacelist-suppress-file-warnings x.interfaces files)
     :programs   (vl-programlist-suppress-file-warnings   x.programs   files)
     :classes    (vl-classlist-suppress-file-warnings     x.classes    files)
     :packages   (vl-packagelist-suppress-file-warnings   x.packages   files)
     :configs    (vl-configlist-suppress-file-warnings    x.configs    files))))

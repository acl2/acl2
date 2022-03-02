; Utilities for making lists of symbols.
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Make a new symbol of the form <pre><sym1><mid><sym2><post> in the PKG package.
(defun pack-symbol-with-symbol (sym1 sym2 pre mid post pkg)
  (declare (xargs :guard (and (symbolp sym1)
                              (symbolp sym2)
                              (stringp pre)
                              (stringp mid)
                              (stringp post)
                              (stringp pkg)
                              (not (equal pkg "")))))
  (intern$ (concatenate 'string pre (symbol-name sym1) mid (symbol-name sym2) post)
           pkg))

;; Make all symbols of the form <pre><sym><mid><sym2><post> in the PKG package,
;; where sym2 is in SYMS.
(defun pack-symbol-with-symbols (sym syms pre mid post pkg)
  (declare (xargs :guard (and (symbolp sym)
                              (symbol-listp syms)
                              (stringp pre)
                              (stringp mid)
                              (stringp post)
                              (stringp pkg)
                              (not (equal pkg "")))))
  (if (endp syms)
      nil
    (cons (pack-symbol-with-symbol sym (first syms) pre mid post pkg)
          (pack-symbol-with-symbols sym (rest syms) pre mid post pkg))))

;; Make all symbols of the form <pre><sym1><mid><sym2><post> in the PKG
;; package, where sym1 is in SYMS1 and where sym2 is in SYMS2.
(defun pack-symbols-with-symbols (syms1 syms2 pre mid post pkg)
  (declare (xargs :guard (and (symbol-listp syms1)
                              (symbol-listp syms2)
                              (stringp pre)
                              (stringp mid)
                              (stringp post)
                              (stringp pkg)
                              (not (equal pkg "")))))
  (if (endp syms1)
      nil
    (append (pack-symbol-with-symbols (first syms1) syms2 pre mid post pkg)
            (pack-symbols-with-symbols (rest syms1) syms2 pre mid post pkg))))

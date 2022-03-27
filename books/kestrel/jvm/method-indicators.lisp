; Indicators for methods that can be elaborated into method-designator-strings
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "method-designator-strings")

(defun method-indicatorp (m)
  (declare (xargs :guard t))
  (stringp m) ;todo: add checks?
  )

;; Makes a list of every method in the METHOD-INFO-ALIST whose name is METHOD-NAME (descriptors may differ).
;; Returns a list of method-descriptor-strings.
(defun methods-matching-name (class-name method-name method-info-alist)
  (declare (xargs :guard (and (method-namep method-name)
                              (class-namep class-name)
                              (method-info-alistp method-info-alist))
                  :guard-hints (("Goal" :in-theory (enable METHOD-INFO-ALISTP))) ;todo
                  ))
  (if (endp method-info-alist)
      nil
    (let* ((entry (first method-info-alist))
           (this-method-id (car entry))
           (this-method-name (method-id-name this-method-id)))
      (if (equal method-name this-method-name)
          (cons (concatenate 'string class-name "." this-method-name (method-id-descriptor this-method-id))
                (methods-matching-name class-name method-name (rest method-info-alist)))
        (methods-matching-name class-name method-name (rest method-info-alist))))))

;; M is at least of the form ClassName.methodName.  The method signature may be
;; omitted if unambiguous, if which case this tool adds it.
;; Returns a method-designator-string.
;; TODO: Consider allowing the package to be omitted, but what if we have a
;; class in an unnamed package and we need to distinguish that from a class
;; in some other package with package omitted (can't treat that as ambiguous)?
(defun elaborate-method-indicator (m class-alist)
  (declare (xargs :guard (and (method-indicatorp m)
                              (alistp class-alist)
                              (all-class-namesp (strip-cars class-alist))
                              (class-info0-listp (strip-cdrs class-alist)))))
  (if (position #\( m)
      ;; A paren is present, so m is unambiguous
      m
    ;; No method descriptor present, so try to find a unique method:
    ;; m might be foo.bar.baz.ClassName.methodName
    (let* ((class-name (acl2::substring-before-last-occurrence m #\.))
           (method-name (acl2::substring-after-last-occurrence m #\.))
           (class-info (acl2::lookup-equal class-name class-alist)))
      (if (not class-info)
          (er hard? 'elaborate-method-indicator "Class not found: ~x0." class-name)
        (if (not (class-infop0 class-info)) ; for guard proof
            (er hard? 'elaborate-method-indicator "Ill-formed class: ~x0." class-name)
          (let ((methods-matching-name (methods-matching-name class-name method-name (class-decl-methods class-info))))
            (if (endp methods-matching-name)
                (er hard? 'elaborate-method-indicator "No methods in ~x0 named ~x1: ~x0." class-name method-name)
              (if (consp (cdr methods-matching-name))
                  (er hard? 'elaborate-method-indicator "More than 1 method in ~x0 named ~x1: ~x0.  Matching methods: ~x2.  Disambiguate by adding a descriptor." class-name method-name methods-matching-name)
                ;; exactly 1 matching method:
                (first methods-matching-name)))))))))

; Support for running ACL2 from the command line on JSON arguments
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Support for running an ACL2 command from the command line, reading the
;; command and its arguments from a .json file.

(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "kestrel/alists-light/lookup-equal-def" :dir :system)
(include-book "kestrel/strings-light/upcase" :dir :system)
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))

(mutual-recursion
  ;; Attempts to convert a parsed-json-value into a corresponding ACL2 value.
  ;; The correspondence is not perfect, e.g., JSON does not have symbols.
  (defun parsed-json-value-to-lisp-value (val)
    (declare (xargs :guard (parsed-json-valuep val)
                    :hints (("Goal" :in-theory (e/d (parsed-json-valuep)
                                                    (acl2-count))))
                    :verify-guards nil ; done below
                    ))
    (cond ((not (mbt (parsed-json-valuep val)))
           nil)
          ((eq :true val) t)
          ((eq :false val) nil)
          ((eq :null val) nil) ; todo: think about this (could go to :null)
          ((rationalp val) val)
          ((stringp val) val) ; todo: look for keywords
          ((parsed-json-arrayp val)
           (parsed-json-values-to-lisp-values (parsed-json-array->values val)))
          ;; must be a json object
          (t
            (let* ((pairs (parsed-json-object->pairs val))
                   (keys (strip-cars pairs)) ;; strings, but we might someday convert some to symbols
                   (vals (strip-cdrs pairs)))
              (pairlis$ (parsed-json-values-to-lisp-values keys)
                        (parsed-json-values-to-lisp-values vals))))))

  (defun parsed-json-values-to-lisp-values (vals)
    (declare (xargs :guard (parsed-json-valuesp vals)))
    (if (endp vals)
        nil
      (cons (parsed-json-value-to-lisp-value (first vals))
            (parsed-json-values-to-lisp-values (rest vals))))))

(verify-guards parsed-json-value-to-lisp-value
  :hints (("Goal" :in-theory (enable parsed-json-valuesp-when-string-listp)
           :expand (parsed-json-valuep val))))

(defthm len-of-parsed-json-values-to-lisp-values
  (equal (len (parsed-json-values-to-lisp-values vals))
         (len vals))
  :hints (("Goal" :expand (parsed-json-values-to-lisp-values vals)
           :induct (len vals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun intern-as-keywords (strs)
  (declare (xargs :guard (string-listp strs)))
  (if (endp strs)
      nil
    (cons (intern (string-upcase-gen (first strs)) "KEYWORD")
          (intern-as-keywords (rest strs)))))

(defthm len-of-intern-as-keywords
  (equal (len (intern-as-keywords strs))
         (len strs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund alternate (keys vals)
  (declare (xargs :guard (and (true-listp keys)
                              (true-listp vals)
                              (= (len keys) (len vals)))))
  (if (endp keys)
      nil
    (cons (first keys) (cons (first vals) (alternate (rest keys) (rest vals))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp event state) where EVENT is the command represented by the
;; JSON file, ready to be run.
(defun run-json-command-fn (file state)
  (declare (xargs :guard t
                  :stobjs state))
  (b* ((ctx 'run-json-command)
       ((when (not (stringp file)))
        (er hard? ctx "Bad filename (must be a string): ~x0." file)
        (mv :bad-filename nil state))
       (- (cw "Running command in ~x0.~%" file))
       ;; Read and parse the JSON:
       ((mv erp val state)
        (parse-file-as-json file state))
       ((when erp)
        (er hard? ctx "Error reading or parsing JSON File ~x0." file)
        (mv :error-reading-or-parsing-file nil state))
       ;; Check that the top-level form is a JSON "object" (a map from keys to values):
       ((when (not (parsed-json-objectp val)))
        (er hard? ctx "File ~x0 does not contain a JSON object (dictionary)." file)
        (mv :invalid-json nil state))
       ;; Check that the keys in the map are exactly "command" and "arguments":
       (pairs (parsed-json-object->pairs val))
       ((when (let ((keys (strip-cars pairs)))
                (not (or (equal '("command" "arguments") keys)
                         ;; not sure if we should allow this:
                         (equal '("arguments" "command") keys)))))
        (er hard? ctx "JSON object should contain exactly 2 keys, \"command\" and \"arguments\".")
        (mv :invalid-json nil state))
       ;; Check the command:
       (command (lookup-equal "command" pairs))
       ((when (not (stringp command)))
        (er hard? ctx "The \"command\" must be a string, but it is ~x0." command)
        (mv :invalid-json nil state))
       ;; Convert the command to a symbol (in the ACL2 package):
       (command (intern (string-upcase-gen command) "ACL2")) ; todo: think about other packages
       ;; Check the arguments, which should be a JSON object (a map):
       (arguments (lookup-equal "arguments" pairs))
       ((when (not (parsed-json-objectp arguments)))
        (er hard? ctx "The \"arguments\" must be a JSON object (dictionary), but it is ~x0" arguments)
        (mv :invalid-json nil state))
       (arg-pairs (parsed-json-object->pairs arguments))
       (arg-names (strip-cars arg-pairs))
       ((when (not (no-duplicatesp-equal arg-names)))
        (er hard? ctx "The \"arguments\" must not contain duplicate keys.")
        (mv :duplicate-keys nil state))
       ;; Convert the arg names to keywords (arg names in the JSON should not include the colons):
       (arg-names (intern-as-keywords arg-names))
       ;; Convert the arg vals to native Lisp vals (lists, etc.):
       (arg-vals (parsed-json-values-to-lisp-values (strip-cdrs arg-pairs)))
       ;; Form the command:
       (event `(,command ,@(alternate arg-names arg-vals))))
    (mv nil event state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Runs the command in FILE, which should contain JSON representing the command
;; and its arguments.
;; Currently, all of the arguments to the command must be keyword arguments.
;; TODO: Support commands that are not events.
(defmacro run-json-command (file)
  `(make-event (run-json-command-fn ,file state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defun rename-filepath (path)
;;   (declare (xargs :guard (stringp path)))
;;   (concatenate 'string path ".new.c")) ; todo: do better (string the extension, etc. ; todo: backup old files

;; (defun rename-filepaths (paths)
;;   (declare (xargs :guard (string-listp paths)))
;;   (if (endp paths)
;;       nil
;;     (cons (rename-filepath (first paths))
;;           (rename-filepaths (rest paths)))))

;; (defun rename-keys-in-filepath-transunit-map (map)
;;   (declare (xargs :guard (c$::filepath-transunit-mapp map)
;;                   :mode :program ;todo
;;                   ))
;;   (omap::from-lists (omap::keys map)
;;                     (omap::values map)))

;; (defun rename-transunit-ensemble (tens)
;;   (declare (xargs :guard (c$::transunit-ensemblep tens)
;;                   :mode :program
;;                   ))
;;   (c$::change-transunit-ensemble tens
;;                                  :unwrap (rename-keys-in-filepath-transunit-map
;;                                            (c$::transunit-ensemble->unwrap tens))))

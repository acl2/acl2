; JVM methods
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; This book deals with our representation of JVM methods.
;; These structures are created by the class-file-parser.

;; (include-book "fields") ;for field-idp
(include-book "instructions")

;(include-book "method-designator-strings") ;todo merge into this book?
;(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)

(local
 (defthm keyword-listp-forward-to-true-listp
   (implies (acl2::keyword-listp x)
            (true-listp x))
   :hints (("Goal" :in-theory (enable acl2::keyword-listp)))))

(local
 (defthm keyword-listp-forward-to-eqlable-listp
   (implies (acl2::keyword-listp x)
            (eqlable-listp x))
   :hints (("Goal" :in-theory (enable acl2::keyword-listp)))))

(in-theory (disable ;acl2::member-of-cons
                    ;acl2::subsetp-car-member
                    acl2::MEMBER-EQUAL)) ;for speed


;; Note that method-namep is defined in instructions.lisp


;compare program counters
(defund pc< (pc1 pc2) (declare (xargs :guard (and (pcp pc1) (pcp pc2)))) (< pc1 pc2))
(defund pc<= (pc1 pc2) (declare (xargs :guard (and (pcp pc1) (pcp pc2)))) (<= pc1 pc2))

;fixme replace the uses of + with something better like inc-pc?
(defthm pcp-of-+
  (implies (and (pcp pc1)
                (pcp pc2))
           (pcp (+ pc1 pc2)))
  :hints (("Goal" :in-theory (enable pcp))))

;these aren't true as stated, if the offset is too negative...
;; (defthm pcp-of-+-offset-version1
;;   (implies (and (pc-offsetp pc1)
;;                 (pcp pc2))
;;            (pcp (+ pc1 pc2)))
;;   :hints (("Goal" :in-theory (enable pcp))))

;; (defthm pcp-of-+-offset-version2
;;   (implies (and (pcp pc1)
;;                 (pc-offsetp pc2))
;;            (pcp (+ pc1 pc2)))
;;   :hints (("Goal" :in-theory (enable pcp))))

;fixme replace the uses of + with something better like inc-pc?
(defthm pcp-of-+-2
  (implies (and (inst-lengthp pc1)
                (pcp pc2))
           (pcp (+ pc1 pc2)))
  :hints (("Goal" :in-theory (enable pcp))))

(defthm pcp-of-+-2-ALT
  (implies (and (inst-lengthp pc1)
                (pcp pc2))
           (pcp (+ pc2 pc1)))
  :hints (("Goal" :in-theory (enable pcp))))



;fixme check that the pcs increment correctly for each instruction
;fixme check that relative jumps are in bounds (or at least don't go negative, which may be enough for now to show the PC is a natp)
(defund jvm-instructions-okayp (program valid-pcs)
  (declare (xargs :guard (and (true-listp valid-pcs)
                              (acl2::all-pcp valid-pcs))))
  (if (atom program)
      (equal program nil)
    (let* ((entry (first program)))
      (and (consp entry)
           (let* ((pc (car entry))
                  (inst (cdr entry)))
             (and (pcp pc)
                  (jvm-instruction-okayp inst pc valid-pcs)
                  (jvm-instructions-okayp (rest program) valid-pcs)))))))

(defthm alistp-when-jvm-instructions-okayp
  (implies (jvm-instructions-okayp program valid-pcs)
           (alistp program))
  :hints (("Goal" :in-theory (enable jvm-instructions-okayp alistp))))

(defthm integer-listp-of-strip-cars-when-jvm-instructions-okayp
  (implies (jvm-instructions-okayp program valid-pcs)
           (integer-listp (strip-cars program)))
  :hints (("Goal" :in-theory (enable jvm-instructions-okayp strip-cars))))

;fixme should this have a guard of true-list?

(defun increasing-pcsp (pcs prev-pc)
  (declare (xargs :guard (and (true-listp pcs)
                              (pcp prev-pc)
                              (acl2::all-pcp pcs))))
  (if (endp pcs)
      t
    (and (pc< prev-pc (first pcs))
         (increasing-pcsp (rest pcs) (first pcs)))))

;todo: constrain to only apply to non-native methods?  should always be preceded by a check?
(defund method-programp (program)
  (declare (xargs :guard t))
  (and (alistp program)
       (let ((pcs (strip-cars program)))
         (and (acl2::all-pcp pcs)
              (consp program)        ;the program cannot be empty
              (eql 0 (first pcs)) ;the first instruction should be at PC 0
              (increasing-pcsp (rest pcs) 0)
              (jvm-instructions-okayp program pcs)))))

;todo: slow?
(defthm alistp-when-method-programp
  (implies (method-programp program)
           (alistp program))
  :hints (("Goal" :in-theory (enable method-programp alistp))))

(defun get-pcs-from-program (program)
  (declare (xargs :guard (method-programp program)))
  (strip-cars program))

(defun empty-program ()
  (declare (xargs :guard t))
  '((0 :return)))

(defthm method-programp-of-empty-program
  (method-programp (empty-program)))

(defun exception-table-entryp (entry)
  (declare (xargs :guard t))
  (and (= 4 (len entry))
       (pcp (first entry)) ;"from" ;todo: check that this is a valid PC in the method
       (pcp (second entry)) ;"to" ;todo: check that this is a valid PC in the method
       (pcp (third entry)) ;"target" ;todo: check that this is a valid PC in the method
       (or (eq :any (fourth entry))
           (class-namep (fourth entry))) ;exception "type"
       ))

;;move to jvm package!
(defun acl2::all-exception-table-entryp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
      (and (jvm::exception-table-entryp (first x))
           (acl2::all-exception-table-entryp (rest x)))))

(defund exception-tablep (table)
  (declare (xargs :guard t))
  (and (true-listp table)
       (acl2::all-exception-table-entryp table)))

(defund local-variable-table-entryp (entry)
  (declare (xargs :guard t))
  (and (true-listp entry)
       (eql 5 (len entry))
       (let ((index (nth 0 entry))
             (start-pc (nth 1 entry))
             (end-pc (nth 2 entry))
             (name (nth 3 entry))
             (type (nth 4 entry)))
         (and (natp index)
              (pcp start-pc)
              (or (eql -1 end-pc) ;for empty range that starts at 0
                  (pcp end-pc))
              (stringp name)
              (typep type)))))

(defun all-local-variable-table-entryp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
      (and (jvm::local-variable-table-entryp (first x))
           (all-local-variable-table-entryp (rest x)))))

(defthm local-variable-table-entryp-of-car
  (implies (all-local-variable-table-entryp entries)
           (equal (jvm::local-variable-table-entryp (car entries))
                  (consp entries)))
  :hints (("Goal" :in-theory (enable all-local-variable-table-entryp))))

(defthm all-local-variable-table-entryp-of-remove-equal
  (implies (all-local-variable-table-entryp entries)
           (all-local-variable-table-entryp (remove-equal entry entries)))
  :hints (("Goal" :in-theory (enable remove-equal all-local-variable-table-entryp))))

(defthm all-local-variable-table-entryp-of-revappend
  (implies (and (all-local-variable-table-entryp entries)
                (all-local-variable-table-entryp acc))
           (all-local-variable-table-entryp (revappend entries acc)))
  :hints (("Goal" :in-theory (enable all-local-variable-table-entryp))))

(defund local-variable-tablep (table)
  (declare (xargs :guard t))
  (and (true-listp table)
       (all-local-variable-table-entryp table)))

(defthm local-variable-tablep-of-cdr
  (implies (local-variable-tablep table)
           (local-variable-tablep (cdr table)))
  :hints (("Goal" :in-theory (enable local-variable-tablep))))

(defthm local-variable-tablep-forward-to-true-listp
  (implies (local-variable-tablep table)
           (true-listp table))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable local-variable-tablep))))

;returns (list name type) for the local, or nil
(defund acl2::lookup-in-local-variable-table (localnum pc local-variable-table)
  (declare (xargs :guard (and (local-variable-tablep local-variable-table)
                              (natp localnum)
                              (natp pc))
                  :guard-hints (("Goal" :in-theory (enable local-variable-tablep
                                                           local-variable-table-entryp)))))
  (if (endp local-variable-table)
      nil
    (let* ((entry (first local-variable-table))
           (slot (nth 0 entry))
           (start-pc (nth 1 entry))
           (end-pc (nth 2 entry))
           (name (nth 3 entry))
           (type (nth 4 entry)))
      (if (and (eql localnum slot)
               (<= start-pc pc)
               (<= pc end-pc))
          (list name type)
        (acl2::lookup-in-local-variable-table localnum pc (rest local-variable-table))))))

(defthm stringp-of-car-of-lookup-in-local-variable-table
  (implies (and (local-variable-tablep local-variable-table)
                (acl2::lookup-in-local-variable-table localnum pc local-variable-table))
           (stringp (car (acl2::lookup-in-local-variable-table localnum pc local-variable-table))))
  :hints (("Goal" :in-theory (enable local-variable-tablep
                                     acl2::lookup-in-local-variable-table
                                     local-variable-table-entryp))))

;;The keys in the method-info alist must be in this list:
(defconst *method-info-keys*
  '(:access-flags
    ;; info from the descriptor:
    :parameter-types
    :return-type
    ;; attributes (or portions thereof):
    :program ;; part of the Code attribute, rename this to :code?
    :max-locals ;; part of the Code attribute
    :exception-table ;; part of the Code attribute
    :line-number-table
    :local-variable-table
    ))

;recognizer for a well formed method-info object
(defund method-infop (method-info)
  (declare (xargs :guard t))
  (and (alistp method-info)
       (acl2::subsetp-eq (strip-cars method-info) *method-info-keys*)
       (let ((access-flags (acl2::lookup-eq :access-flags method-info)))
         (and (acl2::keyword-listp access-flags)
              (acl2::no-duplicatesp access-flags)
              (acl2::subsetp-eq access-flags '(:acc_public
                                               :acc_private
                                               :acc_protected
                                               :acc_static
                                               :acc_final
                                               :acc_synchronized
                                               :acc_bridge
                                               :acc_varargs
                                               :acc_native
                                               :acc_abstract
                                               :acc_strict
                                               :acc_synthetic))
              ;; The program is a well-formed program iff the method is not native or abstract (in either case, it would have no program).
              (if (and (not (acl2::member-eq :acc_native access-flags))
                       (not (acl2::member-eq :acc_abstract access-flags)))
                  (method-programp (acl2::lookup-eq :program method-info))
                (eq :no-program  (acl2::lookup-eq :program method-info)))
              (return-typep (acl2::lookup-eq :return-type method-info))
              (true-listp (acl2::lookup-eq :parameter-types method-info))
              (all-typep (acl2::lookup-eq :parameter-types method-info))
              (let ((max-locals (acl2::lookup-eq :max-locals method-info)))
                (or (not max-locals) (natp max-locals)))
              (local-variable-tablep (acl2::lookup-equal :local-variable-table method-info))
              ;; fixme something about the line-number-table
              (exception-tablep (acl2::lookup-eq :exception-table method-info))))))

;nil should not be a method-info, so that we can use it to indicate failure (failure to look up a method's info)
(defthm not-method-infop-of-nil
  (not (method-infop nil)))

(defthm method-infop-forward-to-true-listp
  (implies (method-infop method-info)
           (true-listp method-info))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable method-infop))))

(defthm method-infop-forward-to-true-listp-of-lookup-eq
  (implies (method-infop method-info)
           (true-listp (acl2::lookup-equal :access-flags method-info)))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable method-infop))))

(defthm method-infop-forward-to-alistp
  (implies (method-infop method-info)
           (alistp method-info))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable method-infop))))

(defthm exception-tablep-of-lookup-equal-of-exception-table
  (implies (method-infop method-info)
           (exception-tablep (acl2::lookup-equal :exception-table method-info)))
  :hints (("Goal" :in-theory (enable method-infop))))

(defund method-access-flags (method-info)
  (declare (xargs :guard (method-infop method-info)))
  (acl2::lookup-eq :access-flags method-info))

(defthm true-listp-of-method-access-flags-forward
  (implies (method-infop method-info)
           (true-listp (method-access-flags method-info)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable method-infop method-access-flags))))

;; TODO: bool-fix these?

(defun method-publicp (method-info)
  (declare (xargs :guard (method-infop method-info)))
  (acl2::member-eq :acc_public (method-access-flags method-info)))

(defun method-privatep (method-info)
  (declare (xargs :guard (method-infop method-info)))
  (acl2::member-eq :acc_private (method-access-flags method-info)))

(defun method-protectedp (method-info)
  (declare (xargs :guard (method-infop method-info)))
  (acl2::member-eq :acc_protected (method-access-flags method-info)))

(defun method-synchronizedp (method-info)
  (declare (xargs :guard (method-infop method-info)))
  (acl2::member-eq :acc_synchronized (method-access-flags method-info)))

(defun method-staticp (method-info)
  (declare (xargs :guard (method-infop method-info)))
  (acl2::member-eq :acc_static (method-access-flags method-info)))

(defun method-nativep (method-info)
  (declare (xargs :guard (method-infop method-info)))
  (acl2::member-eq :acc_native (method-access-flags method-info)))

(defun method-abstractp (method-info)
  (declare (xargs :guard (method-infop method-info)))
  (acl2::member-eq :acc_abstract (method-access-flags method-info)))

(defun method-program (method-info)
  (declare (xargs :guard (method-infop method-info)))
  (acl2::lookup-eq :program method-info))

(defthm method-program-of-acons
  (equal (method-program (acons key val alist))
         (if (equal key :program)
             val
           (method-program alist)))
  :hints (("Goal" :in-theory (enable method-program))))

(defun exception-table (method-info)
  (declare (xargs :guard (method-infop method-info)))
  (acl2::lookup-eq :exception-table method-info))

(defthm method-programp-of-method-program
  (implies (and (method-infop method-info)
                (not (method-nativep method-info))
                (not (method-abstractp method-info)))
           (method-programp (method-program method-info)))
  :hints (("Goal" :in-theory (enable method-infop method-program method-access-flags))))

;this could/should include a method-id?
;a method "designator" is everything we need to uniquely designate a method by "name" (i.e., its class name, method name, and string descriptor)
(defund method-designatorp (obj)
  (declare (xargs :guard t))
  (and (equal 3 (len obj))
       (true-listp obj)
       (class-namep (first obj))
       (method-namep (second obj))
       (method-descriptorp (third obj))))

(defund make-method-designator (class-name method-name method-descriptor)
  (declare (xargs :guard t)) ;fixme do better?
  (list class-name method-name method-descriptor))

(defthm method-designatorp-of-make-method-designator
  (equal (method-designatorp (make-method-designator class-name method-name method-descriptor))
         (and (class-namep class-name)
              (method-namep method-name)
              (method-descriptorp method-descriptor)))
  :hints (("Goal" :in-theory (enable method-designatorp make-method-designator))))

;Make a dummy method with the given program.  Makes it static so we don't have
;to provide an instance.
(defun make-dummy-method-info (program)
  (declare (xargs :guard t)) ;todo
  `((:access-flags . (:acc_static))
    (:program . ,program)
    ;(:parameter-types . nil) ;todo: think about this (the parameter types are used for much) hmmm.  we could move them and the return type to a meta-data section of the method-info (also the local variable table and line number table -- the jvm model doesn't use any of that for anything important)
    (:return-type . :void) ;i guess this is okay
    (:max-locals . 0)
    ;(:local-variable-table . nil)
    ;(:line-number-table . nil)
    ;(:exception-table . nil)
    ))

(defthm method-infop-of-make-dummy-method-info
  (implies (method-programp program)
           (method-infop (make-dummy-method-info program)))
  :hints (("Goal" :in-theory (enable method-infop))))

(defthm true-listp-of-lookup-equal-of-parameter-type-when-method-infop
  (implies (method-infop method-info)
           (true-listp (acl2::lookup-equal :parameter-types method-info)))
  :hints (("Goal" :in-theory (enable method-infop))))

(defthm all-typep-of-lookup-equal-of-parameter-type-when-method-infop
  (implies (method-infop method-info)
           (all-typep (acl2::lookup-equal :parameter-types method-info)))
  :hints (("Goal" :in-theory (enable method-infop))))

(defthm local-variable-tablep-of-lookup-equal-of-parameter-type-when-method-infop
  (implies (method-infop method-info)
           (local-variable-tablep (acl2::lookup-equal :local-variable-table method-info)))
  :hints (("Goal" :in-theory (enable method-infop))))

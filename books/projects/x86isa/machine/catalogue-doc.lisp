; x86isa categorized listings of implemented/unimplemented instructions
;
; X86ISA Library
; Copyright (C) 2024 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Sol Swords (sswords@gmail.com)

(in-package "X86ISA")

(include-book "inst-doc")
(include-book "catalogue-data")





(defines sdm-instruction-table-elide
  ;; this is just so we can look at the hierarchy of topics without seeing everything
  (define sdm-instruction-table-elide ((x sdm-instruction-table-p))
    :measure (sdm-instruction-table-count x)
    :returns (new-x sdm-instruction-table-p)
    :verify-guards nil
    (b* ((x (sdm-instruction-table-fix x)))
      (if (atom x)
          nil
        (cons (cons (caar x) (sdm-instruction-table-entry-elide (cdar x)))
              (sdm-instruction-table-elide (cdr x))))))
  (define sdm-instruction-table-entry-elide ((x sdm-instruction-table-entry-p))
    :measure (sdm-instruction-table-entry-count x)
    :returns (new-x sdm-instruction-table-entry-p)
    (b* (((sdm-instruction-table-entry x)))
      (change-sdm-instruction-table-entry x :subsecs (sdm-instruction-table-elide x.subsecs)
                                          :implemented nil :unimplemented nil :doc "")))
  ///
  (verify-guards sdm-instruction-table-elide))

(define section-number-string-aux ((x nat-listp)
                                   (acc str::printtree-p))
  :returns (str stringp :rule-classes :type-prescription)
  (if (atom x)
      (str::printtree->str acc)
    (section-number-string-aux (cdr x)
                               (str::pcat acc (str::natstr (car x))
                                          (if (consp (cdr x)) "." "")))))

(define section-number-string ((x nat-listp))
  (section-number-string-aux x nil))

(define sdm-instruction-table-entry-topicname ((section nat-listp)
                                               (x sdm-instruction-table-entry-p))
  (intern-in-package-of-symbol (str::cat (section-number-string section) " "
                                         (sdm-instruction-table-entry->title x))
                               'x86isa-package))

(define sdm-instruction-table-instruction-counts ((x sdm-instruction-table-p))
  :measure (sdm-instruction-table-count x)
  :returns (mv (impl-count natp :rule-classes :type-prescription)
               (unimpl-count natp :rule-classes :type-prescription))
  :verify-guards nil
  (b* ((x (sdm-instruction-table-fix x))
       ((when (atom x)) (mv 0 0))
       ((sdm-instruction-table-entry entry) (cdar x))
       ((mv sub-impl sub-unimpl) (sdm-instruction-table-instruction-counts entry.subsecs))
       ((mv rest-impl rest-unimpl) (sdm-instruction-table-instruction-counts (cdr x))))
    (mv (+ (len entry.implemented) sub-impl rest-impl)
        (+ (len entry.unimplemented) sub-unimpl rest-unimpl)))
  ///
  (verify-guards sdm-instruction-table-instruction-counts))

(define create-sdm-subsec-summary-aux ((x sdm-instruction-table-p)
                                       (acc str::printtree-p))
  :returns (new-acc str::printtree-p)
  (b* (((when (atom x))
        (str::printtree-fix acc))
       ((unless (mbt (and (consp (car x)) (nat-listp (caar x)))))
        (create-sdm-subsec-summary-aux (cdr x) acc))
       ((cons section (sdm-instruction-table-entry entry)) (car x))
       (acc (str::pcat acc "<tr><td>@(see |" (symbol-name (sdm-instruction-table-entry-topicname section entry)) "|)</td>"))
       ((mv sub-impl sub-unimpl) (sdm-instruction-table-instruction-counts entry.subsecs))
       (impl (+ (len entry.implemented) sub-impl))
       (unimpl (+ (len entry.unimplemented) sub-unimpl))
       (acc (str::pcat acc "<td>" (str::natstr impl) "</td>"))
       (acc (str::pcat acc "<td>" (str::natstr unimpl) "</td>"))
       (acc (str::pcat acc "<td>" (str::natstr (+ impl unimpl)) "</td></tr>" #\Newline)))
    (create-sdm-subsec-summary-aux (cdr x) acc)))
           

(define create-sdm-subsec-summary ((x sdm-instruction-table-p))
  (b* ((acc nil)
       (acc (str::pcat acc
                       "<table> <th>Subsection</th> <th>Implemented</th> <th>Unimplemented</th> <th>Total</th>"
                       #\Newline))
       (acc (create-sdm-subsec-summary-aux x acc))
       (acc (str::pcat acc "</table>" #\Newline)))
    (str::printtree->str acc)))
  

(define sdm-instruction-entry-xdoc ((topicname symbolp)
                                    (x sdm-instruction-table-entry-p)
                                    (parent symbolp))
  (b* (((sdm-instruction-table-entry x))
       ((mv sub-impl sub-unimpl) (sdm-instruction-table-instruction-counts x.subsecs)))
    `((defxdoc ,topicname
        :parents (,parent)
        :long ,(str::cat x.doc acl2::*newline-string*
                         (if x.unimplemented
                             (str::cat "<h3>Unimplemented Instructions</h3>" acl2::*newline-string*
                                       (create-insts-doc x.unimplemented :full-opcode? t)
                                       acl2::*newline-string*)
                           "")
                         (if x.implemented
                             (str::cat
                              "<h3>Implemented Instructions</h3>" acl2::*newline-string*
                              (create-insts-doc x.implemented :full-opcode? t)
                              acl2::*newline-string*)
                           "")
                         (if x.subsecs
                             (str::cat "<h3>Subsections</h3>"
                                       "<p>Total instructions: " (str::natstr (+ sub-impl sub-unimpl))
                                       ", Implemented: " (str::natstr sub-impl)
                                       ", Unimplemented: " (str::natstr sub-unimpl)
                                       "</p>" acl2::*newline-string*
                                       (create-sdm-subsec-summary x.subsecs))
                           "")))
      ;; Order subtopics in the order defined
      (xdoc::order-subtopics ,topicname nil t))))

(define sdm-instruction-table-xdoc-events ((x sdm-instruction-table-p)
                                           (parent symbolp))
  ;; Run on organized instruction table
  :measure (sdm-instruction-table-count x)
  (b* ((x (sdm-instruction-table-fix x))
       ((when (atom x)) nil)
       ((cons section (sdm-instruction-table-entry entry)) (car x))
       (topicname (sdm-instruction-table-entry-topicname section entry))
       (doc1 (sdm-instruction-entry-xdoc topicname entry parent))
       (subsec-docs (sdm-instruction-table-xdoc-events entry.subsecs topicname)))
    (append doc1 subsec-docs (sdm-instruction-table-xdoc-events (cdr x) parent))))




(defxdoc  sdm-instruction-set-summary
  :parents (x86isa)
  :short "Summary of what instructions are implemented/unimplemented, as organized in the
Instruction Set Summary of the Intel Software Developer Manual (volume 1
chapter 5)."
  :long (b* ((subsecs
              (sdm-instruction-table-organize
               (table-alist 'sdm-instruction-sect (w state))))
             ((mv sub-impl sub-unimpl)
              (sdm-instruction-table-instruction-counts subsecs)))
          (str::cat
           "<p>Note: this summary is based on the opcode maps (see @(see implemented-opcodes) and subtopics).
To the extent that the opcode maps are incomplete (as noted in several of the
below topics), the instruction counts listed below and in subtopics are as
well.</p>"

           "<h3>Subsections</h3>"
                  "<p>Total instructions: " (str::natstr (+ sub-impl sub-unimpl))
                  ", Implemented: " (str::natstr sub-impl)
                  ", Unimplemented: " (str::natstr sub-unimpl)
                  "</p>" acl2::*newline-string*
                  (create-sdm-subsec-summary subsecs))))


(with-output :off (event)
  (make-event
   (b* ((table (table-alist 'sdm-instruction-sect (w state))))
     (cons 'progn (sdm-instruction-table-xdoc-events
                   (sdm-instruction-table-organize table)
                   'sdm-instruction-set-summary)))))

#|
(include-book
 "xdoc/save" :dir :system)

(xdoc::save "catalogue-manual" :redef-okp t)
|#




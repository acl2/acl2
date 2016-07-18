; count.lsp
;
; I use this script in order to count how many events are in the ACL2 books.
; This approach, and the function count-events-through, was developed by
; Peter Dillinger in response to an email I sent to the ACL2 help list, and
; is presumably in the public domain.
;
; Instructions:
;
;    ./modified-acl2
;    (ld "count.lsp")
;
; This loads a bunch of books and eventually prints a bunch of statistics.
; It takes a few minutes to run.

(in-package "ACL2")
(set-verify-guards-eagerness 2)

; Can't do anything about the ttag notes, but this clears up some output.
(set-inhibit-output-lst '(error warning warning! observation prove proof-builder event expansion summary proof-tree))

(defun symbol-to-nat-alistp (x)
  (declare (xargs :guard t))
 (or (null x)
     (and (consp x)
          (consp (car x))
          (symbolp (caar x))
          (natp (cdar x))
          (symbol-to-nat-alistp (cdr x)))))

(defun inc-nat-alist (key alist)
 (declare (xargs :guard (and (symbolp key)
                             (symbol-to-nat-alistp alist))))
 (cond ((endp alist)
        (list (cons key 1)))
       ((eq key (caar alist))
        (cons (cons key (1+ (cdar alist)))
              (cdr alist)))
       (t
        (cons (car alist)
              (inc-nat-alist key (cdr alist))))))

(defthm symbol-to-nat-alistp--inc-nat-alist
 (implies (and (symbolp key)
               (symbol-to-nat-alistp alist))
          (symbol-to-nat-alistp (inc-nat-alist key alist))))

(defun count-events-through1 (cur-wrld end-wrld alist)
 (declare (xargs :guard (and (worldp cur-wrld)
                             (worldp end-wrld)
                             (symbol-to-nat-alistp alist))))
 (cond ((or (endp cur-wrld)
            (equal cur-wrld end-wrld))
        alist)
       ((and (eq (first (car cur-wrld)) 'event-landmark)
             (eq (second (car cur-wrld)) 'global-value)
             (consp (cddr (car cur-wrld)))
             (consp (cdddr (car cur-wrld))))
        (let ((key (cond ((and (consp (fourth (car cur-wrld)))
                               (symbolp (car (fourth (car cur-wrld)))))
                          (car (fourth (car cur-wrld))))
                         ((symbolp (fourth (car cur-wrld)))
                          (fourth (car cur-wrld)))
                         (t
                          'unknown))))
          (count-events-through1 (cdr cur-wrld)
                                 end-wrld
                                 (inc-nat-alist key
                                                alist))))
       (t
        (count-events-through1 (cdr cur-wrld)
                               end-wrld
                               alist))))

(defun count-events-through (start-wrld end-wrld)
 (declare (xargs :guard (and (worldp start-wrld)
                             (worldp end-wrld))))
 (count-events-through1 start-wrld end-wrld nil))

; The basic approach is to save the world, then load the "top" book for each
; directory, and save the world again.  Then we can count the number of events
; added by each set of includes.

(assign start-wrld (w state))

(include-book "utilities/top" :ttags :all)
(assign util-wrld (w state))

(include-book "logic/top" :ttags :all)
(assign logic-wrld (w state))

(include-book "build/top" :ttags :all)
(assign build-wrld (w state))

; There isn't a top book for clauses, so we just load everything
(include-book "clauses/split" :ttags :all)
(include-book "clauses/compiler" :ttags :all)
(include-book "clauses/clean-clauses" :ttags :all)
(include-book "clauses/update-clause-iff-bldr" :ttags :all)
(include-book "clauses/update-clause-bldr" :ttags :all)
(include-book "clauses/disjoined-update-clause-bldr" :ttags :all)
(include-book "clauses/smart-negate" :ttags :all)
(include-book "clauses/split-bldr" :ttags :all)
(assign clause-wrld (w state))

(include-book "rewrite/assms/top" :ttags :all)
(assign assms-wrld (w state))

(include-book "rewrite/crewrite-clause" :ttags :all)
(include-book "rewrite/fast-crewrite-clause" :ttags :all)
(include-book "rewrite/urewrite-clause" :ttags :all)
(include-book "rewrite/theory-arities" :ttags :all)
(include-book "rewrite/traces/trace-arities" :ttags :all)
(include-book "rewrite/gather" :ttags :all)
(assign rewrite-wrld (w state))

(include-book "tactics/compiler" :ttags :all)
(assign tactic-wrld (w state))

(include-book "interface/top" :ttags :all)
(assign iface-wrld (w state))



(cw "Utilities directory stats: ~%~x0~%"
    (count-events-through (@ util-wrld) (@ start-wrld)))

(cw "Logic directory stats: ~%~x0~%"
    (count-events-through (@ logic-wrld) (@ util-wrld)))

(cw "Build directory stats: ~%~x0~%"
    (count-events-through (@ build-wrld) (@ logic-wrld)))

(cw "Clauses directory stats: ~%~x0~%"
    (count-events-through (@ clause-wrld) (@ build-wrld)))

(cw "Assms directory stats: ~%~x0~%"
    (count-events-through (@ assms-wrld) (@ clause-wrld)))

(cw "Rewrite directory stats: ~%~x0~%"
    (count-events-through (@ rewrite-wrld) (@ assms-wrld)))

(cw "Tactic directory stats: ~%~x0~%"
    (count-events-through (@ tactic-wrld) (@ rewrite-wrld)))

(cw "Interface directory stats: ~%~x0~%"
    (count-events-through (@ iface-wrld) (@ tactic-wrld)))


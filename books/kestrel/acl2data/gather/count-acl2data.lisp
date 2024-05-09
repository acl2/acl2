; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; 6/2022: For run6, retry with removal of everything I've considered so far:
; hyp, hint, book-runes, single-rune.

; 5/2022: Only remove book-runes.  Code that formerly was conditioned on
; #+acl2-runes is now restored, but is for remove-book-runes-checkpoints rather
; than remove-rune-checkpoints.  Many uses of rune-alist below now reference an
; alist mapping book names (generally relativized to "[books]/") to rune lists,
; rather than whatever rune-alist was for the obsolete remove-rune-checkpoints
; code, which is somewhat out of date.

; 4/2022: Restricted to removing hypotheses and hints, not runes.  In case we
; want to remove runes again, we are using feature :acl2-runes to mark code
; that should be included if we want to include rune removal.

(in-package "ACL2")

(defrec acl2data
; WARNING: Keep this the same as this record definition in patch.lsp.
  ((hyp-alist hint-setting-alist . book-runes-alist)
   ((hash expansion-stack goal . goal-clauses) event . rule-classes)
   (used-induction . rune-alist)
   . symbol-table)
  nil)

(program) ; avoid specifying guards

(defun count-acl2data-1 (alist fail total)
  (cond ((endp alist) (mv fail total))
        ((eq (cadr (car alist)) :remove)
         (count-acl2data-1 (cdr alist) fail (1+ total)))
        (t
         (count-acl2data-1 (cdr alist) (1+ fail) (1+ total)))))

(defun count-acl2data (acl2data)
  (mv-let (hint-f hint-t)
    (count-acl2data-1 (access acl2data acl2data :hint-setting-alist) 0 0)
    (mv-let (hyp-f hyp-t)
      (count-acl2data-1 (access acl2data acl2data :hyp-alist) 0 0)
      (mv-let (book-runes-f book-runes-t)
        (count-acl2data-1 (access acl2data acl2data :book-runes-alist) 0 0)
        (mv-let (single-rune-f single-rune-t)
          (count-acl2data-1 (access acl2data acl2data :rune-alist) 0 0)
          (mv hint-f hint-t hyp-f hyp-t book-runes-f book-runes-t
              single-rune-f single-rune-t))))))

(defun count-acl2data-alist (alist)

; Alist is a mapping from event names to acl2data records.  We add up the
; number of entries in each of the fields of each record that correspond to a
; failed proof when removing the relevant item (hypothesis, hint, or
; book-runes, or rune) in the car of each entry.  E.g., let's call this br-f
; for removing runes of an included book.  Similarly, we add up the totals
; (including both failure and success) and obtain br-t.  Then we return (mv
; ... br-f br-t ...), where the ellipses represent the other kinds of removal.

  (cond ((endp alist)
         (mv 0 0 0 0 0 0 0 0))
        (t (mv-let (hint-f-1 hint-t-1 hyp-f-1 hyp-t-1
                             book-runes-f-1 book-runes-t-1
                             single-rune-f-1 single-rune-t-1)
             (count-acl2data (cdar alist))
             (mv-let (hint-f-2 hint-t-2 hyp-f-2 hyp-t-2
                               book-runes-f-2 book-runes-t-2
                               single-rune-f-2 single-rune-t-2)
               (count-acl2data-alist (cdr alist))
               (mv (+ hint-f-1 hint-f-2)
                   (+ hint-t-1 hint-t-2)
                   (+ hyp-f-1 hyp-f-2)
                   (+ hyp-t-1 hyp-t-2)
                   (+ book-runes-f-1 book-runes-f-2)
                   (+ book-runes-t-1 book-runes-t-2)
                   (+ single-rune-f-1 single-rune-f-2)
                   (+ single-rune-t-1 single-rune-t-2)))))))

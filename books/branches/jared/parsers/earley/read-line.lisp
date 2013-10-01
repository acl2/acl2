; ACL2 Parser for Java
; Copyright (C) 2013 Battelle Memorial Institute
;
; Contact:
;  David Rager, ragerdl@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")

(include-book "std/io/base" :dir :system)
(include-book "cutil/define" :dir :system)

; These used to go through but aren't anymore.  We don't need them now, so I'm
; commenting them out.

;; (defun read-line$1 (line channel state)
;;   (declare (xargs :guard (and (symbolp channel)
;;                               (open-input-channel-p channel
;;                                                     :character state)
;;                               (character-listp line))
;;                   :stobjs (state)
;;                   :measure (file-measure channel state)))
;;   (b* (((unless (mbt (state-p state)))
;;         (mv nil state))
;;        ((mv char state)
;;         (read-char$ channel state))
;;        ((unless char)
;;         (let ((line (reverse (coerce line 'string))))
;;           (mv line state)))

;;        ((when (eql char #\Newline))
;;         (let ((line (reverse (coerce line 'string))))
;;           (mv line state)))

;;        (line (cons char line)))
;;     (read-line$1 line channel state)))

;; (defthm stringp-of-read-line$1
;;   (implies (and (symbolp channel)
;;                 (open-input-channel-p channel :character state)
;;                 (state-p state))
;;            (stringp (mv-nth 0 (read-line$1 line channel state)))))

;; (defun read-line$ (channel state)
;;   (declare (xargs :guard (and (symbolp channel)
;;                               (open-input-channel-p channel
;;                                                     :character state))
;;                   :stobjs (state)
;;                   :measure (file-measure channel state)))
;;   (read-line$1 nil channel state))

;; (defthm stringp-of-read-line$
;;   (implies (and (symbolp channel)
;;                 (open-input-channel-p channel
;;                                       :character state)
;;                 (state-p state))
;;            (stringp (mv-nth 0 (read-line$ channel state)))))

;; I leave the following definition of an example of how formal methods helped
;; us catch the bug that if the car of file-input is newline, that we should
;; return (cdr file-input), not just file-input.

;;; (define read-line!1 ((file-input character-listp))
;;;   :returns (mv (line character-listp
;;;                      "The characters from the next line of the file input"
;;;                      :hyp :fguard)
;;;                (new-file-input character-listp "The rest of the file input"
;;;                :hyp :fguard))
;;;   (cond ((or (atom file-input)
;;;              (equal (car file-input) #\Newline))
;;;          (mv nil file-input))
;;;         (t (mv-let (recursive-chars remainder-of-file-input)
;;;              (read-line!1 (cdr file-input))
;;;              (mv (cons (car file-input)
;;;                        recursive-chars)
;;;                  remainder-of-file-input)))))

(define read-line!1 ((file-input character-listp))
  :returns (mv (line character-listp
                     "The characters from the next line of the file input"
                     :hyp :fguard)
               (new-file-input character-listp "The rest of the file input"
                               :hyp :fguard))
  (cond ((atom file-input)
         (mv nil file-input))
        ((equal (car file-input) #\Newline)
         ;; read-line!1 has no characters to return
         (mv nil (cdr file-input)))
        (t (mv-let (recursive-chars remainder-of-file-input)
             (read-line!1 (cdr file-input))
             (mv (cons (car file-input)
                       recursive-chars)
                 remainder-of-file-input))))
  ///

  (defthm read-line!1-weak
    (<= (acl2-count (mv-nth 1 (read-line!1 file-input)))
        (acl2-count file-input))
    :rule-classes :linear)


  (local
   (defthm read-line!1-strong-lemma
     (implies (and (consp file-input)
                   (not (mv-nth 0 (read-line!1 (cdr file-input))))
                   (characterp (car file-input))
                   (character-listp (cdr file-input))
                   (not (equal (car file-input) #\newline))
                   (list (car file-input)))
              (< (acl2-count (mv-nth 1 (read-line!1 (cdr file-input))))
                 (acl2-count file-input)))
     :rule-classes (:rewrite :linear)))
  (local
   (defun recur-on-cdr-only (x)
     (if (atom x)
         nil
       (cons 1
             (recur-on-cdr-only (cdr x))))))

  (defthm read-line!1-strong
    (implies (mv-nth 0 (read-line!1 file-input))
             (< (acl2-count (mv-nth 1 (read-line!1 file-input)))
                (acl2-count file-input)))
    :hints (("Goal" :induct (recur-on-cdr-only file-input)))
    :rule-classes :linear))

;; (local
;;  (defthm lemma
;;    (implies (and (consp file-input)
;;                  (not (character-listp (car file-input)))
;;                  (not (mv-nth 0 (read-line!1 (cdr file-input))))
;;                  (characterp (car file-input))
;;                  (character-listp (cdr file-input))
;;                  (not (equal (car file-input) #\newline))
;;                  (list (car file-input)))
;;             (< (acl2-count (mv-nth 1 (read-line!1 (cdr file-input))))
;;                (+ 1 (acl2-count (car file-input))
;;                   (acl2-count (cdr file-input)))))))

;; (local
;;  (defthm lemmmaa
;;    (implies
;;     (and (consp file-input)
;;          (implies (and (character-listp (car file-input))
;;                        (mv-nth 0 (read-line!1 (car file-input))))
;;                   (< (acl2-count (mv-nth 1 (read-line!1 (car file-input))))
;;                      (acl2-count (car file-input))))
;;          (implies (and (character-listp (cdr file-input))
;;                        (mv-nth 0 (read-line!1 (cdr file-input))))
;;                   (< (acl2-count (mv-nth 1 (read-line!1 (cdr file-input))))
;;                      (acl2-count (cdr file-input)))))
;;     (implies (and (character-listp file-input)
;;                   (mv-nth 0 (read-line!1 file-input)))
;;              (< (acl2-count (mv-nth 1 (read-line!1 file-input)))
;;                 (acl2-count file-input))))))

;; (local
;;  (defthm read-line!1-strong-lemma
;;    (implies (and (consp file-input)
;;                  (not (mv-nth 0 (read-line!1 (cdr file-input))))
;;                  (characterp (car file-input))
;;                  (character-listp (cdr file-input))
;;                  (not (equal (car file-input) #\newline))
;;                  (list (car file-input)))
;;             (<= (acl2-count (mv-nth 1 (read-line!1 (cdr file-input))))
;;                 (acl2-count file-input)))
;;    :rule-classes (:rewrite :linear)))


(define read-line! ((file-input character-listp))
; consider renaming to read-line-as-char-list
  :returns (mv (line stringp "The string read from the next line of the file input"
                     :hyp :fguard)
               (new-file-input character-listp "The rest of the file input"
                               :hyp :fguard))
  (mv-let (chars new-file-input)
    (read-line!1 file-input)
    (mv (coerce chars 'string)
        new-file-input))
  ///

  (defthm read-line!-weak
    (<= (acl2-count (mv-nth 1 (read-line! file-input)))
        (acl2-count file-input)))

  (defthm read-line!-strong-but-with-an-inner-hyp
    (implies (mv-nth 0 (read-line!1 file-input))
             (< (acl2-count (mv-nth 1 (read-line! file-input)))
                (acl2-count file-input))))

  (defthm read-line!-strong

; This is a silly lemma, as read-line!-strong-alternative is probably more
; meaningful.  But, I'm leaving it for now and can clean it up later.

    (implies (< 0 (length (mv-nth 0 (read-line! file-input))))
             (< (acl2-count (mv-nth 1 (read-line! file-input)))
                (acl2-count file-input)))
    :hints (("Goal" :use ((:instance read-line!-strong-but-with-an-inner-hyp)))))

  (defthm read-line!-strong-alternative
    (implies (not (equal (mv-nth 0 (read-line! file-input)) ""))
             (< (acl2-count (mv-nth 1 (read-line! file-input)))
                (acl2-count file-input)))
    :hints (("Goal" :use ((:instance read-line!-strong-but-with-an-inner-hyp))))))

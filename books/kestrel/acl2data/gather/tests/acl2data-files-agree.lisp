; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Run (chk-all-test-files state) to check that test__acl2data.out and
; test__acl2data.out.saved agree up to filenames, and similarly for test2 etc.
; The list of tests is in the final definition in this file; update it when
; adding more tests.

(in-package "ACL2")

(program)
(set-state-ok t)

; For "STD" package:
(include-book "std/portcullis" :dir :system)

(defun acl2data-out-alist (filename state)
  (state-global-let*
; We'll report any read-file error ourselves.
   ((inhibit-output-lst (cons 'error (@ inhibit-output-lst))))
   (mv-let (erp val state)
     (read-file filename state)
     (mv erp (cdr (car (last val))) state))))

(defun hint-setting-alist-equal (a1 a2)

; This is only relevant for advice runs, where the last

  (cond
    ((or (endp a1) (endp a2))
     (and (endp a1) (endp a2)))
    (t (let* ((entry1 (car a1))
              (entry2 (car a2)))
         (cond ((or (eq (caar a1) :remove)
                    (eq (caar a2) :remove))
                (and (equal (car a1) (car a2))
                     (hint-setting-alist-equal (cdr a1) (cdr a2))))
               ((equal (butlast entry1 1) (butlast entry2 1))
                (and (iff (car (last entry1)) (car (last entry2)))
                     (hint-setting-alist-equal (cdr a1) (cdr a2))))
               (t nil))))))

(defun acl2data-alists-agree-1 (name a1 a2 warnp advice-p acc)

; Warnp is nil or a filename.  Acc is t at the top level.

  (cond
   #+skip
   ((and (consp a1)
         (or (eq (caar a1) :HASH)
             (eq (caar a1) :EXPANSION-STACK)))
    (acl2data-alists-agree-1 name (cdr a1) a2 warnp advice-p acc))
   ((or (endp a1) (endp a2))
    (if (and (endp a1) (endp a2))
        acc
      (if warnp
          (cw "~%~x0: Extra alist entry ~x1 for name ~x2"
              warnp
              (if (endp a1) (car a2) (car a1))
              name)
        (er hard 'acl2data-alists-agree-1
            "~%~x0: Extra alist entry ~x1 for name ~x2"
            warnp
            (if (endp a1) (car a2) (car a1))
            name))))
   (t (let* ((doublet1 (car a1))
             (key1 (car doublet1))
             (doublet2 (car a2))
             (key2 (car doublet2))
             (val (and (eq key1 key2)
                       (cond
                         ((eq key1 :RUNE-ALIST)
                          (set-equalp-equal (cadr doublet1)
                                            (cadr doublet2)))
                         ((eq key1 :SYMBOL-TABLE)
                          (equal (strip-cars (cadr doublet1))
                                 (strip-cars (cadr doublet2))))
                         ((and advice-p
                               (eq key1 :HINT-SETTING-ALIST))
; The advice stuff changes enough that I'll be content that we get advice in
; the new run iff we got advice in the old run.
                          (hint-setting-alist-equal (cadr doublet1) (cadr doublet2)))
                         (t
                          (equal (cadr doublet1) (cadr doublet2)))))))
        (prog2$
         (or val
             (if warnp
                 (cw "~%~x0: Difference for name ~x1 at key ~x2"
                     warnp name key1)
               (er hard 'acl2data-alists-agree-1
                   "~%~x0: Difference for name ~x1 at key ~x2"
                   warnp name key1)))
         (acl2data-alists-agree-1 name (cdr a1) (cdr a2) warnp advice-p
                                  (and val acc)))))))

(defun acl2data-alists-agree (a1 a2 warnp advice-p acc)
  (cond ((endp a1) acc)
        (t (let ((acc (acl2data-alists-agree-1 (caar a1) (cdar a1) (cdar a2)
                                               warnp advice-p acc)))
             (acl2data-alists-agree (cdr a1) (cdr a2) warnp advice-p acc)))))

(defun acl2data-files-agree (f1 f2 warnp advice-p state)
  (mv-let (erp1 a1 state)
    (acl2data-out-alist f1 state)
    (mv-let (erp2 a2 state)
      (acl2data-out-alist f2 state)
      (cond
       ((or erp1 erp2)
        (cond (warnp (prog2$
                      (cw "~%Unable to read file ~#0~[~x1~/~@1~]"
                          (if (and erp1 erp2) 1 0)
                          (cond ((null erp1) f2)
                                ((null erp2) f1)
                                (t (msg "~x0 or file ~x1" f1 f2))))
                      (value nil)))
              (t (er soft 'acl2data-files-agree
                     "Unable to read file ~#0~[~x1~/~@1~]"
                     (if (and erp1 erp2) 1 0)
                     (cond ((null erp1) f2)
                           ((null erp2) f1)
                           (t (msg "~x0 or file ~x1" f1 f2)))))))
       ((equal (strip-cars a1) (strip-cars a2))
        (value (acl2data-alists-agree a1 a2 warnp advice-p t)))
       (warnp (prog2$
               (cw "~%Different event names!~|~%~x0:~|~X14~|~%~x2:~|~X34"
                   f1 (strip-cars a1)
                   f2 (strip-cars a2)
                   nil)
               (value nil)))
       (t (er soft 'acl2data-files-agree
              "Different event names!~|~%~x0:~|~X14~|~%~x2:~|~X34"
              f1 (strip-cars a1)
              f2 (strip-cars a2)
              nil))))))

(defun chk-test-files (name warnp advice-p state)
  (let ((test-file (concatenate 'string "runs/" name "__acl2data.out"))
        (result-file (concatenate 'string
                                  (if advice-p "expected-advice/" "expected/")
                                  name
                                  "__acl2data.out.saved")))
    (cond ((eq advice-p :skip)
           (mv-let (erp ign state)
             (state-global-let*
              ((inhibit-output-lst (cons 'error (@ inhibit-output-lst))))
              (read-file test-file state))
             (declare (ignore ign))
             (cond (erp (value t))
                   (warnp (prog2$ (cw "~%File ~x0 should not exist, but does."
                                      test-file)
                                  (value nil)))
                   (t (er soft 'chk-test-files
                          "~%File ~x0 should not exist, but does."
                          test-file)))))
          (t (acl2data-files-agree test-file result-file (and warnp name)
                                   advice-p state)))))

(defun chk-all-test-files (state)

; For advice runs: Since test3, test4, and test6 don't have any :hints, but
; advice runs only remove hints, the corresponding .out files shouldn't exist.

  (er-let* ((adv (getenv! "ACL2_ADVICE" state))
            (val1 (chk-test-files "test" t adv state))
            (val2 (chk-test-files "test2" t adv state))
            (val2a (chk-test-files "test2a" t adv state))
            (val2b (chk-test-files "test2b" t adv state))
            (val3 (chk-test-files "test3" t (and adv :skip) state))
            (val3a (chk-test-files "test3a" t adv state))
            (val4 (chk-test-files "test4" t (and adv :skip) state))
            (val5 (chk-test-files "test5" t adv state))
            (val6 (chk-test-files "test6" t (and adv :skip) state))
            (val7a (chk-test-files "test7a" t adv state))
            (val7b (chk-test-files "test7b" t adv state))
            (val8 (chk-test-files "test8" t adv state))
; test9 is really slow to do using advice, so we skip it in that case.
            (val9 (chk-test-files "test9" t (and adv :skip) state)))
    (pprogn (newline *standard-co* state)
            (if (and val1 val2 val2a val2b val3 val3a val4 val5 val6
                     val7a val7b val8 val9)
                (value 'TESTS-SUCCEEDED)
              (value (list "test" val1
                           "test2" val2
                           "test2a" val2a
                           "test2b" val2b
                           "test3" val3
                           "test3a" val3a
                           "test4" val4
                           "test5" val5
                           "test6" val6
                           "test7a" val7a
                           "test7b" val7b
                           "test8" val8))))))

; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../xid")
(include-book "../pattern-white-space")
(include-book "../bidi-controls")
(include-book "../normalization")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book defines a function that writes, to a file,
; what the functions of this library return for EVERY code point,
; in a version of Unicode.
; The file is then compared with the files that independent implementations
; of the same version of Unicode write in the same format:
; see the file README.md in this directory.
;
; The file has a header line and then one line for each code point,
; from 0 to #x10FFFF, with these fields, separated by semicolons:
;
;   cp      the code point
;   xids    1 if it has XID_Start, 0 otherwise
;   xidc    1 if it has XID_Continue, 0 otherwise
;   pws     1 if it has Pattern_White_Space, 0 otherwise
;   bidic   1 if it has Bidi_Control, 0 otherwise
;   bidif   its Bidi_Class if that is one of the explicit directional
;           formatting classes (LRE, RLE, LRO, RLO, PDF, LRI, RLI, FSI, PDI),
;           - otherwise
;   ccc     its Canonical_Combining_Class
;   fce     1 if it has Full_Composition_Exclusion, 0 otherwise
;   dm      its Decomposition_Mapping, as in UnicodeData.txt:
;           c: and the mapping if it is canonical,
;           k: and the mapping if it is a compatibility one,
;           - if there is none
;   nfd     the NFD form of the code point alone
;   nfc     the NFC form of the code point alone
;   nfkd    the NFKD form of the code point alone
;   nfkc    the NFKC form of the code point alone
;
; Numbers are in decimal; the code points of a sequence are separated
; by spaces.
;
; This book also defines a function that writes, to another file,
; what the library says about pairs of code points: whether they compose,
; and what the NFC form of the pair is.  The pairs are all the pairs
; (first, second) such that FIRST is the first code point of some pair
; that composes and SECOND is the second code point of some pair that
; composes (including the pairs that compose to Hangul syllables);
; so the file has all the pairs that compose, and many more that do not.
; Each line has the two code points, the code point they compose to
; (or - if they do not compose), and the NFC form of the pair,
; separated by spaces.
;
; The functions here are in program mode: they do input/output,
; and they are not part of the library proper.

(program)

(defun dump-nats (nats channel state)
  (declare (xargs :stobjs state))
  (cond ((endp nats) state)
        (t (pprogn (princ$ (car nats) channel state)
                   (if (consp (cdr nats))
                       (princ$ " " channel state)
                     state)
                   (dump-nats (cdr nats) channel state)))))

(defun dump-flag (flag channel state)
  (declare (xargs :stobjs state))
  (princ$ (if flag ";1" ";0") channel state))

(defun dump-code-point (cp ver channel state)
  (declare (xargs :stobjs state))
  (b* ((cps (list cp))
       (state (princ$ cp channel state))
       (state (dump-flag (xid-start-p cp ver) channel state))
       (state (dump-flag (xid-continue-p cp ver) channel state))
       (state (dump-flag (pattern-white-space-p cp ver) channel state))
       (state (dump-flag (bidi-control-p cp ver) channel state))
       (class (bidi-formatting-class cp ver))
       (state (princ$ ";" channel state))
       (state (princ$ (if class
                          (symbol-name (bidi-formatting-class-kind class))
                        "-")
                      channel state))
       (state (princ$ ";" channel state))
       (state (princ$ (canonical-combining-class cp ver) channel state))
       (state (dump-flag (full-composition-exclusion-p cp ver) channel state))
       ((mv canonical mapping) (decomposition-mapping cp ver))
       (state (princ$ (cond (canonical ";c:")
                            (mapping ";k:")
                            (t ";-"))
                      channel state))
       (state (dump-nats mapping channel state))
       (state (princ$ ";" channel state))
       (state (dump-nats (nfd cps ver) channel state))
       (state (princ$ ";" channel state))
       (state (dump-nats (nfc cps ver) channel state))
       (state (princ$ ";" channel state))
       (state (dump-nats (nfkd cps ver) channel state))
       (state (princ$ ";" channel state))
       (state (dump-nats (nfkc cps ver) channel state)))
    (newline channel state)))

(defun dump-code-points (cp ver channel state)
  (declare (xargs :stobjs state))
  (cond ((> cp #x10FFFF) state)
        (t (pprogn (dump-code-point cp ver channel state)
                   (dump-code-points (+ 1 cp) ver channel state)))))

; Write the file.  For example:
;   (dump-properties (version-v16.0.0) "/tmp/acl2-16.0.0.txt" state)

(defun dump-properties (ver filename state)
  (declare (xargs :stobjs state))
  (b* (((mv channel state) (open-output-channel filename :character state))
       ((unless channel)
        (prog2$ (er hard? 'dump-properties "Cannot open ~x0." filename)
                state))
       (state (princ$ "#cp;xids;xidc;pws;bidic;bidif;ccc;fce;dm;"
                      channel state))
       (state (princ$ "nfd;nfc;nfkd;nfkc" channel state))
       (state (newline channel state))
       (state (dump-code-points 0 ver channel state)))
    (close-output-channel channel state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The first and the second code points of the canonical decomposition
; mappings of the primary composites among the code points of a list.

(defun composing-firsts-and-seconds (cps ver firsts seconds)
  (cond ((endp cps) (mv firsts seconds))
        (t (b* ((cp (car cps))
                (mapping (decomposition-map-lookup cp
                                                   (canonical-mappings ver)))
                (composes (and (equal (len mapping) 2)
                               (not (full-composition-exclusion-p cp ver)))))
             (composing-firsts-and-seconds
              (cdr cps)
              ver
              (if composes (cons (first mapping) firsts) firsts)
              (if composes (cons (second mapping) seconds) seconds))))))

(defun nats-from (start step count)
  (cond ((zp count) nil)
        (t (cons start (nats-from (+ start step) step (- count 1))))))

(defun dump-pairs-of-first (first seconds ver channel state)
  (declare (xargs :stobjs state))
  (cond ((endp seconds) state)
        (t (b* ((second (car seconds))
                (composite (composition first second ver))
                (state (princ$ first channel state))
                (state (princ$ " " channel state))
                (state (princ$ second channel state))
                (state (princ$ " " channel state))
                (state (princ$ (or composite "-") channel state))
                (state (princ$ " " channel state))
                (state (dump-nats (nfc (list first second) ver)
                                  channel state))
                (state (newline channel state)))
             (dump-pairs-of-first first (cdr seconds) ver channel state)))))

(defun dump-pairs-of-firsts (firsts seconds ver channel state)
  (declare (xargs :stobjs state))
  (cond ((endp firsts) state)
        (t (pprogn (dump-pairs-of-first (car firsts) seconds ver channel state)
                   (dump-pairs-of-firsts (cdr firsts) seconds ver
                                         channel state)))))

; Write the file.  For example:
;   (dump-pairs (version-v16.0.0) "/tmp/acl2-pairs-16.0.0.txt" state)

(defun dump-pairs (ver filename state)
  (declare (xargs :stobjs state))
  (b* (((mv channel state) (open-output-channel filename :character state))
       ((unless channel)
        (prog2$ (er hard? 'dump-pairs "Cannot open ~x0." filename)
                state))
       ((mv firsts seconds)
        (composing-firsts-and-seconds (all-code-points) ver nil nil))
       (firsts (append
                (remove-duplicates firsts)
                ;; the leading consonants and the LV syllables:
                (nats-from *hangul-l-base* 1 *hangul-l-count*)
                (nats-from *hangul-s-base*
                           *hangul-t-count*
                           (* *hangul-l-count* *hangul-v-count*))))
       (seconds (append
                 (remove-duplicates seconds)
                 ;; the vowels and the trailing consonants:
                 (nats-from *hangul-v-base* 1 *hangul-v-count*)
                 (nats-from (+ 1 *hangul-t-base*) 1 (- *hangul-t-count* 1))))
       (state (princ$ "#first second composite nfc" channel state))
       (state (newline channel state))
       (state (dump-pairs-of-firsts firsts seconds ver channel state)))
    (close-output-channel channel state)))

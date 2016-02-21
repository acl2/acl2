;; Shilpi Goel

x86-fetch-decode-execute: Step function
x86-run: Run function

(defthm x86-fetch-decode-execute-and-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (xlate-equiv-x86s (x86-fetch-decode-execute x86-1)
                             (x86-fetch-decode-execute x86-2)))
  :rule-classes :congruence)

(defthm x86-run-and-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (xlate-equiv-x86s (x86-run n x86-1)
                             (x86-run n x86-2)))
  :rule-classes :congruence)

(defthm x86-fetch-decode-execute-opener-in-system-level-mode
  (implies
   (and (other-hyps-tbd)
        (not (xr :programmer-level-mode 0 x86)))
   (xlate-equiv-x86s
    (x86-fetch-decode-execute x86)
    (top-level-opcode-execute
     start-rip temp-rip3 prefixes rex-byte opcode/escape-byte modr/m sib x86))))

(defthm x86-run-opener-not-ms-not-zp-n
  ;; Pre-existing x86-run opener rule.
  (implies (and (not (ms x86))
                (not (fault x86))
                (syntaxp (quotep n))
                (not (zp n)))
           (equal (x86-run n x86)
                  (x86-run (1- n) (x86-fetch-decode-execute x86)))))

The key here is x86-fetch-decode-execute-and-xlate-equiv-x86s. Note
that proving this rule would require proving similar congruence rules
about each instruction semantic function.

Key to x86-fetch-decode-execute-and-xlate-equiv-x86s is to prove rules
about rm08 and wm08 with xlate-equiv-x86s.

(defthm mv-nth-2-rm08-and-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth 2 (rm08 lin-addr r-w-x x86-1))
                  (mv-nth 2 (rm08 lin-addr r-w-x x86-2))))
  :rule-classes :congruence)

(defthm mv-nth-2-wm08-and-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth 1 (wm08 lin-addr value x86-1))
                  (mv-nth 1 (wm08 lin-addr value x86-2))))
  :rule-classes :congruence)

(defthm xlate-equiv-x86s-and-xw-mem
  (implies (and
            (xlate-equiv-x86s x86-1 x86-2)
            (system-level-state-p x86-1)
            (system-level-state-p x86-2)
            (physical-address-p index)
            (unsigned-byte-p 8 value))
           (xlate-equiv-x86s
            (xw :mem index value x86-1)
            (xw :mem index value x86-2))))

Is xlate-equiv-x86s-and-xw-mem really a theorem?

Case 1: index is an address disjoint from the paging structures.
        xlate-equiv-x86s-and-xw-mem is a theorem.


Case 2: index is an address of/in some paging entry.

Is
(gather-all-paging-structure-qword-addresses (xw :mem index value x86-1)) ==
(gather-all-paging-structure-qword-addresses (xw :mem index value x86-2))?

1. xlate-equiv-structures-and-gather-pml4-table-qword-addresses:
   (gather-pml4-table-qword-addresses (xw :mem index value x86)) ==
   (gather-pml4-table-qword-addresses x86)

2. gather-qword-addresses-corresponding-to-entries-and-xw-mem:
   (gather-qword-addresses-corresponding-to-entries
    pml4-table-qword-addresses (xw :mem index value x86-1)) ==
   (gather-qword-addresses-corresponding-to-entries
    pml4-table-qword-addresses (xw :mem index value x86-2))

3.
  (gather-qword-addresses-corresponding-to-entries
   pdpt-table-qword-addresses (xw :mem index value x86-1)) ==
  (gather-qword-addresses-corresponding-to-entries
   pdpt-table-qword-addresses (xw :mem index value x86-2))

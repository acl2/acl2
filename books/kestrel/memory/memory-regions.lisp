; Representing memory regions and their contents
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X") ; todo pull out of x86

(include-book "kestrel/x86/portcullis" :dir :system) ; for the package
(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/bv-lists/byte-listp-def" :dir :system)
(local (include-book "kestrel/lists-light/reverse" :dir :system))

;; Recognizes a representation of a memory region, of the form:
;; (<len> <addr> <bytes>)
;; todo: consider adding support for zero-fill (or partial zero-fill) regions
(defund memory-regionp (reg)
  (declare (xargs :guard t))
  (and (true-listp reg)
       (= 3 (len reg))
       (natp (first reg)) ; length
       ;; The ultimate address might be relative (a term representing some base-var plus the addr):
       (natp (second reg)) ; addr (agnostic on the size of the memory space, for now)
       (acl2::byte-listp (third reg))
       ;; the length must be correct, at least for now:
       (= (first reg) (len (third reg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a true-list of memory regions
(defund memory-regionsp (regions)
  (declare (xargs :guard t))
  (if (not (consp regions))
      (null regions)
    (and (memory-regionp (first regions))
         (memory-regionsp (rest regions)))))

(defthm memory-regionsp-of-revappend
  (implies (and (memory-regionsp x)
                (memory-regionsp y))
           (memory-regionsp (revappend x y)))
  :hints (("Goal" :in-theory (enable revappend memory-regionsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Strips out just the addresses and lens
(defund memory-region-addresses-and-lens (regions acc)
  (declare (xargs :guard (and (memory-regionsp regions)
                              (alistp acc))
                  :guard-hints (("Goal" :in-theory (enable memory-regionsp
                                                           memory-regionp)))))
  (if (endp regions)
      (reverse acc)
    (b* ((region (first regions))
         (length (first region))
         (addr (second region))
         ;;(bytes (third region))
         )
      (memory-region-addresses-and-lens (rest regions)
                                        (acons addr length acc)))))

(defthm alistp-of-memory-region-addresses-and-lens
  (implies (alistp acc)
           (alistp (memory-region-addresses-and-lens regions acc)))
  :hints (("Goal" :in-theory (enable memory-region-addresses-and-lens))))

(defthm nat-listp-of-strip-cdrs-of-memory-region-addresses-and-lens
  (implies (and (memory-regionsp regions)
;                  (true-listp acc)
                (nat-listp (strip-cdrs acc)))
           (nat-listp (strip-cdrs (memory-region-addresses-and-lens regions acc))))
  :hints (("Goal" :in-theory (enable memory-region-addresses-and-lens
                                     memory-regionsp
                                     memory-regionp))))

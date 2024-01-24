; An evaluator for x86 code lifting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../evaluator-basic")

(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ;for canonical-address-p$inline

(defund x86isa::n03$inline-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::n03$inline (ifix x)))

(defthm n03$inline-unguarded-correct
  (equal (x86isa::n03$inline-unguarded x)
         (x86isa::n03$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n03$inline-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::4bits-fix-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::4bits-fix (loghead 4 (ifix x))))

(defthm 4bits-fix-unguarded-correct
  (equal (x86isa::4bits-fix-unguarded x)
         (x86isa::4bits-fix x))
  :hints (("Goal" :in-theory (enable x86isa::4bits-fix-unguarded X86ISA::4BITS-FIX))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::8bits-fix-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::8bits-fix (loghead 8 (ifix x))))

(defthm 8bits-fix-unguarded-correct
  (equal (x86isa::8bits-fix-unguarded x)
         (x86isa::8bits-fix x))
  :hints (("Goal" :in-theory (enable x86isa::8bits-fix-unguarded X86ISA::8BITS-FIX))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::PREFIXES-FIX$INLINE-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::PREFIXES-FIX$INLINE (acl2::loghead$inline 52 (ifix x))))

(defthm PREFIXES-FIX$inline-unguarded-correct
  (equal (x86isa::PREFIXES-FIX$inline-unguarded x)
         (x86isa::PREFIXES-FIX$inline x))
  :hints (("Goal" :in-theory (enable x86isa::PREFIXES-FIX$inline-unguarded X86ISA::PREFIXES-FIX))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund loghead$inline-unguarded (n x)
  (declare (xargs :guard t))
  (loghead$inline (nfix n) (ifix x)))

(defthm loghead$inline-unguarded-correct
  (equal (loghead$inline-unguarded n x)
         (loghead$inline n x))
  :hints (("Goal" :in-theory (enable loghead$inline-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *axe-evaluator-x86-fns-and-aliases*
  (append '(x86isa::canonical-address-p$inline ; unguarded
            ;; todo: X86ISA::PREFIXES->OPR$INLINE, logbitp
            (lookup lookup-equal-unguarded)
            (x86isa::n03$inline x86isa::n03$inline-unguarded)
            (x86isa::4bits-fix x86isa::4bits-fix-unguarded)
            (x86isa::8bits-fix x86isa::8bits-fix-unguarded)
            (loghead$inline loghead$inline-unguarded)
            (x86isa::prefixes-fix$inline x86isa::prefixes-fix$inline-unguarded)
            power-of-2p
            logmaskp
            )
          *axe-evaluator-basic-fns-and-aliases*))

;; Makes the evaluator (also checks that each alias given is equivalent to its function):
(make-evaluator-simple x86 *axe-evaluator-x86-fns-and-aliases*)

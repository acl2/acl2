(in-package "X86ISA")

(defun deserialize-page (i j k obj mem$c)
  (declare (xargs :stobjs (mem$c)))
  (b* (((when (not obj)) mem$c)
       ((list* head tail) obj)
       (mem$c (bigmem::write-mem$c (+ (* (+ (* i *num-level-entries*) j)
                                         *num-page-entries*) k)
                                   head mem$c)))
    (deserialize-page i j (1- k) tail mem$c)))

(defun deserialize-l1 (i obj mem$c)
  (declare (xargs :stobjs (mem$c)))
  (b* (((list* head tail) obj)
       ((cons j serialized) head)
       (mem$c (deserialize-page i j (1- *num-page-entries*)
                                serialized mem$c)))
    (if (equal j 0)
	mem$c
      (deserialize-l1 i tail mem$c))))

(defun deserialize-level1s (obj mem$c)
  (declare (xargs :stobjs (mem$c)
		  :guard (good-mem$cp mem$c)))
  (b* (((when (not obj)) mem$c)
       ((list* head tail) obj)
       ((cons idx serialized) head)
       (mem$c (deserialize-l1 idx serialized mem$c)))
    (deserialize-level1s tail mem$c)))

(defun deserialize-mem$c (obj mem$c)
  (declare (xargs :stobjs (mem$c)
                  :guard (good-mem$cp mem$c)))
  (deserialize-level1s obj mem$c))

(defun serialize-mem (x86)
  (stobj-let ((bigmem::mem (mem$c x86)))
             (obj)
             (bigmem::serialize-mem$c bigmem::mem)
             obj))

(defun deserialize-mem (obj x86)
  (stobj-let ((bigmem::mem (mem$c x86)))
             (bigmem::mem)
             (deserialize-mem$c obj bigmem::mem)
             x86))

(defun save-x86 (filename x86)
  (let ((*print-readably* t))
    (with-open-file (str filename
                         :direction :output
                         :if-exists :supersede)
        (print (serialize-x86 x86) str)
      (terpri str))
    nil))

(defun restore-x86 (filename x86)
  (with-open-file (str filename
                       :direction :input)
      (deserialize-x86 (read str) x86)))

;; This is a debugging utility that searches for a given sequence of bytes
;; in every allocated page of memory at a given offset into the page
;; this is meant to help debugging issues with paging

;; Note: throughout this code, pages can mean one of two things:
;; 1. a 4096 byte aligned chunk of memory
;; 2. a 2^20 byte aligned chunk of memory
;; The former definition is used by the x86 paging system, while
;; the latter is used by bigmem in its internal structure

(in-package "X86ISA")

(include-book "machine/state")

(defun starts-with (prefix other)
  (declare (xargs :mode :program))
  (cond ((not prefix) t)
        ((not other) nil)
        (t (and (equal (car prefix)
                       (car other))
                (starts-with (cdr prefix)
                             (cdr other))))))

;; Note: this function busts bigmem pages
(defun mem-bust-page (page bytes offset i1 i2 off)
  (declare (xargs :mode :program))
  (if (not page)
      nil
      (or (if (starts-with bytes (nthcdr offset page))
              (prog2$ (cw "i1: ~x0 i2: ~x1 off: ~x2~%" i1 i2 off) t)
              nil)
          (mem-bust-page (nthcdr 4096 page) bytes offset i1 i2 (+ 4096 off)))))

(defun mem-bust-pages (pages bytes offset i1)
  (declare (xargs :mode :program))
  (if (not pages)
      nil
      ;; Reverse because the list of bytes is in reverse order
      (or (mem-bust-page (reverse (cdar pages)) bytes offset i1 (caar pages) 0)
          (mem-bust-pages (cdr pages) bytes offset i1))))

(defun mem-bust-l1s (l1s bytes offset)
  (declare (xargs :mode :program))
  (if (not l1s)
      nil
      (or (mem-bust-pages (cdar l1s) bytes offset (caar l1s))
          (mem-bust-l1s (cdr l1s) bytes offset))))

(defun mem-buster (bytes offset x86)
  (declare (xargs :mode :program
                  :stobjs (x86)))
  ;; We serialize the mem so we can look through
  ;; only the allocated pages instead of having to
  ;; go through the entire address space
  (b* ((serialized (serialize-mem x86)))
      (mem-bust-l1s serialized bytes offset)))

;; Shilpi Goel

(in-package "X86ISA")

;; Syscall numbers defined as constants

;; ===================================================================

;; A convenient macro to define a constant as one value on linux
;; systems and maybe another on darwin systems:

(defmacro OS (l d)
  #+(and linux (not (or darwin bsd)))
  (declare (ignore d))
  #+(and linux (not (or darwin bsd)))
  l
  #+(and (or darwin bsd) (not linux))
  (declare (ignore l))
  #+(and (or darwin bsd) (not linux))
  d
  )

;; ======================================================================

;; For Linux systems: See /usr/include/x86_64-linux-gnu/asm/unistd_64.h
;; For Darwin systems: See /usr/include/sys/syscall.h

;;                                   Linux Darwin
(defconst       *SYS_read*       (os    0   #x2000003))
(defconst       *SYS_write*      (os    1   #x2000004))
(defconst       *SYS_open*       (os    2   #x2000005))
(defconst       *SYS_close*      (os    3   #x2000006))
(defconst       *SYS_stat*       (os    4   #x20000BC))
(defconst       *SYS_fstat*      (os    5   #x20000BD))
(defconst       *SYS_lstat*      (os    6   #x20000BE))
(defconst       *SYS_lseek*      (os    8   #x20000C7))
(defconst       *SYS_dup*        (os   32   #x200001B))
(defconst       *SYS_dup2*       (os   33   #x200005A))
(defconst       *SYS_fcntl*      (os   72   #x200005C))
(defconst       *SYS_truncate*   (os   76   #x20000C8))
(defconst       *SYS_ftruncate*  (os   77   #x20000C9))
(defconst       *SYS_link*       (os   86   #x2000009))
(defconst       *SYS_unlink*     (os   87   #x200000A))
(defconst       *SYS_fadvise64*  (os  221   -1))
(defconst       *SYS_dup3*       (os  292   -1))

;; For raw mode functions:

;;                                        Linux            Darwin
(defconst       *SYS_read-raw*       (os    0   (- *SYS_read*      #x2000000)))
(defconst       *SYS_write-raw*      (os    1   (- *SYS_write*     #x2000000)))
(defconst       *SYS_open-raw*       (os    2   (- *SYS_open*      #x2000000)))
(defconst       *SYS_close-raw*      (os    3   (- *SYS_close*     #x2000000)))
(defconst       *SYS_stat-raw*       (os    4   (- *SYS_stat*      #x2000000)))
(defconst       *SYS_fstat-raw*      (os    5   (- *SYS_fstat*     #x2000000)))
(defconst       *SYS_lstat-raw*      (os    6   (- *SYS_lstat*     #x2000000)))
(defconst       *SYS_lseek-raw*      (os    8   (- *SYS_lseek*     #x2000000)))
(defconst       *SYS_dup-raw*        (os   32   (- *SYS_dup*       #x2000000)))
(defconst       *SYS_dup2-raw*       (os   33   (- *SYS_dup2*      #x2000000)))
(defconst       *SYS_fcntl-raw*      (os   72   (- *SYS_fcntl*     #x2000000)))
(defconst       *SYS_truncate-raw*   (os   76   (- *SYS_truncate*  #x2000000)))
(defconst       *SYS_ftruncate-raw*  (os   77   (- *SYS_ftruncate* #x2000000)))
(defconst       *SYS_link-raw*       (os   86   (- *SYS_link*      #x2000000)))
(defconst       *SYS_unlink-raw*     (os   87   (- *SYS_unlink*    #x2000000)))
(defconst       *SYS_fadvise64-raw*  (os  221   -1))
(defconst       *SYS_dup3-raw*       (os  292   -1))

;; ======================================================================

;; For raw functions requesting the size of a structure
(defconst       *STRUCT_STAT*        1)

;; ======================================================================

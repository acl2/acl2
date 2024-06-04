; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

; cert_param: (uses-cpp)

(include-book "../read-files")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Without preprocessing.

;;;;;;;;;;;;;;;;;;;;

(read-files :const *stdbool*
            :files ("stdbool.c"))

(read-files :const *stdint*
            :files ("stdint.c"))

(read-files :const *stdbool-stdint*
            :files ("stdbool.c"
                    "stdint.c"))

;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal
 (acl2::nats=>string (filedata->unwrap
                      (omap::lookup (filepath "stdbool.c")
                                    (fileset->unwrap *stdbool-stdint*))))
 "#include <stdbool.h>

int main(void) {
  return (int)false;
}
")

;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal
 (acl2::nats=>string (filedata->unwrap
                      (omap::lookup (filepath "stdint.c")
                                    (fileset->unwrap *stdbool-stdint*))))
 "#include <stdint.h>

int main(void) {
  uint32_t x = 0;
  return 0;
}
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; With preprocessing.

;;;;;;;;;;;;;;;;;;;;

(read-files :const *stdbool-pp*
            :files ("stdbool.c")
            :preprocess t)

(read-files :const *stdint-pp*
            :files ("stdint.c")
            :preprocess t)

(read-files :const *stdbool-stdint-pp*
            :files ("stdbool.c"
                    "stdint.c")
            :preprocess t)

;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal
 (acl2::nats=>string (filedata->unwrap
                      (omap::lookup (filepath "stdbool.c")
                                    (fileset->unwrap *stdbool-stdint-pp*))))
 "









int main(void) {
  return (int)0;
}

")

;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal
 (acl2::nats=>string (filedata->unwrap
                      (omap::lookup (filepath "stdint.c")
                                    (fileset->unwrap *stdbool-stdint-pp*))))
 "


// AIX system headers need stdint.h to be re-enterable while _STD_TYPES_T
// is defined until an inclusion of it without _STD_TYPES_T occurs, in which
// case the header guard macro is defined.



   


// C99 7.18.3 Limits of other integer types
//
//  Footnote 219, 220: C++ implementations should define these macros only when
//  __STDC_LIMIT_MACROS is defined before <stdint.h> is included.
//
//  Footnote 222: C++ implementations should define these macros only when
//  __STDC_CONSTANT_MACROS is defined before <stdint.h> is included.
//
// C++11 [cstdint.syn]p2:
//
//  The macros defined by <cstdint> are provided unconditionally. In particular,
//  the symbols __STDC_LIMIT_MACROS and __STDC_CONSTANT_MACROS (mentioned in
//  footnotes 219, 220, and 222 in the C standard) play no role in C++.
//
// C11 removed the problematic footnotes.
//
// Work around this inconsistency by always defining those macros in C++ mode,
// so that a C library implementation which follows the C99 standard can be
// used in C++.















typedef signed char           int8_t;



typedef short                   int16_t;



typedef int                     int32_t;



typedef long long               int64_t;






typedef unsigned char uint8_t;




typedef unsigned short uint16_t;




typedef unsigned int uint32_t;




typedef unsigned long long uint64_t;



typedef int8_t           int_least8_t;
typedef int16_t         int_least16_t;
typedef int32_t         int_least32_t;
typedef int64_t         int_least64_t;
typedef uint8_t         uint_least8_t;
typedef uint16_t       uint_least16_t;
typedef uint32_t       uint_least32_t;
typedef uint64_t       uint_least64_t;



typedef int8_t            int_fast8_t;
typedef int16_t          int_fast16_t;
typedef int32_t          int_fast32_t;
typedef int64_t          int_fast64_t;
typedef uint8_t          uint_fast8_t;
typedef uint16_t        uint_fast16_t;
typedef uint32_t        uint_fast32_t;
typedef uint64_t        uint_fast64_t;













   






                                        



   



   





   



   



   



   



   






   



   



	#define __deprecated_msg(_msg) __attribute__((__deprecated__(_msg)))



	#define __deprecated_enum_msg(_msg) __deprecated_msg(_msg)





   










   



   




   



   



   



   



   



   






   



   






















   



   



   



   






   









   













   







   



































































































































































































































































































   











   



























   





   



   



                                          


   



   



   



   



   




   





   







   





















   











   



















   


typedef __signed char           __int8_t;

typedef unsigned char           __uint8_t;
typedef short                   __int16_t;
typedef unsigned short          __uint16_t;
typedef int                     __int32_t;
typedef unsigned int            __uint32_t;
typedef long long               __int64_t;
typedef unsigned long long      __uint64_t;

typedef long                    __darwin_intptr_t;
typedef unsigned int            __darwin_natural_t;


   

typedef int                     __darwin_ct_rune_t;     


   
typedef union {
	char            __mbstate8[128];
	long long       _mbstateL;                      
} __mbstate_t;

typedef __mbstate_t             __darwin_mbstate_t;     


typedef long int        __darwin_ptrdiff_t;     



typedef long unsigned int           __darwin_size_t;        



typedef __builtin_va_list       __darwin_va_list;       



typedef int          __darwin_wchar_t;       


typedef __darwin_wchar_t        __darwin_rune_t;        


typedef int           __darwin_wint_t;        


typedef unsigned long           __darwin_clock_t;       
typedef __uint32_t              __darwin_socklen_t;     
typedef long                    __darwin_ssize_t;       
typedef long                    __darwin_time_t;        








   



typedef __int64_t       __darwin_blkcnt_t;      
typedef __int32_t       __darwin_blksize_t;     
typedef __int32_t       __darwin_dev_t;         
typedef unsigned int    __darwin_fsblkcnt_t;    
typedef unsigned int    __darwin_fsfilcnt_t;    
typedef __uint32_t      __darwin_gid_t;         
typedef __uint32_t      __darwin_id_t;          
typedef __uint64_t      __darwin_ino64_t;       

typedef __darwin_ino64_t __darwin_ino_t;        

typedef __darwin_natural_t __darwin_mach_port_name_t; 
typedef __darwin_mach_port_name_t __darwin_mach_port_t; 
typedef __uint16_t      __darwin_mode_t;        
typedef __int64_t       __darwin_off_t;         
typedef __int32_t       __darwin_pid_t;         
typedef __uint32_t      __darwin_sigset_t;      
typedef __int32_t       __darwin_suseconds_t;   
typedef __uint32_t      __darwin_uid_t;         
typedef __uint32_t      __darwin_useconds_t;    
typedef unsigned char   __darwin_uuid_t[16];
typedef char    __darwin_uuid_string_t[37];








// pthread opaque structures


struct __darwin_pthread_handler_rec {
	void (*__routine)(void *);	// Routine to call
	void *__arg;			// Argument to pass
	struct __darwin_pthread_handler_rec *__next;
};

struct _opaque_pthread_attr_t {
	long __sig;
	char __opaque[56];
};

struct _opaque_pthread_cond_t {
	long __sig;
	char __opaque[40];
};

struct _opaque_pthread_condattr_t {
	long __sig;
	char __opaque[8];
};

struct _opaque_pthread_mutex_t {
	long __sig;
	char __opaque[56];
};

struct _opaque_pthread_mutexattr_t {
	long __sig;
	char __opaque[8];
};

struct _opaque_pthread_once_t {
	long __sig;
	char __opaque[8];
};

struct _opaque_pthread_rwlock_t {
	long __sig;
	char __opaque[192];
};

struct _opaque_pthread_rwlockattr_t {
	long __sig;
	char __opaque[16];
};

struct _opaque_pthread_t {
	long __sig;
	struct __darwin_pthread_handler_rec  *__cleanup_stack;
	char __opaque[8176];
};

typedef struct _opaque_pthread_attr_t __darwin_pthread_attr_t;
typedef struct _opaque_pthread_cond_t __darwin_pthread_cond_t;
typedef struct _opaque_pthread_condattr_t __darwin_pthread_condattr_t;
typedef unsigned long __darwin_pthread_key_t;
typedef struct _opaque_pthread_mutex_t __darwin_pthread_mutex_t;
typedef struct _opaque_pthread_mutexattr_t __darwin_pthread_mutexattr_t;
typedef struct _opaque_pthread_once_t __darwin_pthread_once_t;
typedef struct _opaque_pthread_rwlock_t __darwin_pthread_rwlock_t;
typedef struct _opaque_pthread_rwlockattr_t __darwin_pthread_rwlockattr_t;
typedef struct _opaque_pthread_t *__darwin_pthread_t;











   





   

   












typedef unsigned char           u_int8_t;



typedef unsigned short                  u_int16_t;



typedef unsigned int            u_int32_t;



typedef unsigned long long      u_int64_t;



typedef int64_t                 register_t;









typedef unsigned long           uintptr_t;







typedef u_int64_t               user_addr_t;
typedef u_int64_t               user_size_t;
typedef int64_t                 user_ssize_t;
typedef int64_t                 user_long_t;
typedef u_int64_t               user_ulong_t;
typedef int64_t                 user_time_t;
typedef int64_t                 user_off_t;









typedef u_int64_t               syscall_arg_t;






typedef __darwin_intptr_t       intptr_t;









typedef long int intmax_t;




typedef long unsigned int uintmax_t;










   






   





































               












int main(void) {
  uint32_t x = 0;
  return 0;
}

")



(funcdef int64_2_32 (x) (block (return (si (bits x 31 0) 32))))(funcdef uint64_2_32 (x) (block (return (si (bits x 31 0) 32))))(funcdef uint64_2_u32 (x) (block (return (bits x 31 0))))(funcdef int64_2_i32 (x) (block (return (si (bits x 31 0) 32))))(funcdef int2bool (x) (block (return (log<> x 0))))(funcdef bool2uint (x) (block (return (log<> x 0))))

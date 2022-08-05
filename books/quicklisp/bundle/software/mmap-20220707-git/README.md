## About MMAP
This is a utility library providing access to the `mmap` family of functions in a portable way. It should work on Posix and Windows systems. `mmap` allows you to directly map a file into the address space of your process without having to manually read it into memory sequentially. Typically this is much more efficient for files that are larger than a few Kb.

## Supported operations
The library offers access to the following functions:

* `mmap`
* `munmap`
* `msync`
* `mprotect`

It also provides a convenience macro called `with-mmap` to perform safe, local mappings of files.

    (mmap:with-mmap (addr fd size #p"/etc/lsb-release")
      (with-output-to-string (out)
        (loop for i from 0 below size
              for char = (code-char (cffi:mem-aref addr :char i))
              do (write-char char out))))


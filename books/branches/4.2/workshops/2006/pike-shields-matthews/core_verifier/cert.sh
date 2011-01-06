echo "(add-include-book-dir :super-ihs \"/Users/leepike/shade/aamp/model/super-ihs/\") \
(add-include-book-dir :books \"/Users/leepike/shade/acl2_scratch/core_verifier/books/\")" \
> books/cert.acl2

cp books/cert.acl2 ./factorial/
cp books/cert.acl2 ./Fibonacci/
cp books/cert.acl2 ./TEA/
cp books/cert.acl2 ./RC6/
cp books/cert.acl2 ./AES/


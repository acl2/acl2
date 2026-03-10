How the executables were created:

docker run --rm -v .:/src arm32v7/alpine sh -c "apk add gcc musl-dev && gcc -marm -static -o /src/add.elf32-musl-static /src/add.c"

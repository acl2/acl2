
CC = gcc

C_FILES = sat-input-formater \
          smt-prep \
          zchaff-output-formater \
          minisat-output-formater

#C_FILES_C := $(C_FILES:%=%.c)

all: ${C_FILES}

clean:
	rm -f $(C_FILES) *~ #*#

$(C_FILES): %: %.c
	${CC} -o${@} ${@}.c


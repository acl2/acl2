CC = gcc
LD = gcc
CFLAGS = -ggdb -Wall -Wpedantic -Ideps/xed/obj/wkit/include -MMD -fsanitize=address
LDFLAGS = -Ldeps/xed/obj/wkit/lib -lxed -fsanitize=address
LDLIBS = -lxed
RM = /bin/rm -f
OBJS = $(subst .c,.o,*.c)

testgen: $(OBJS) deps/xed/obj/wkit/lib/libxed.a
	$(LD) $(LDFLAGS) $(OBJS) $(LDLIBS) -o testgen

deps/xed:
	git clone git@github.com:intelxed/xed.git deps/xed

deps/mbuild:
	git clone git@github.com:intelxed/mbuild.git deps/mbuild

deps/xed/obj/wkit/lib/libxed.a: deps/xed deps/mbuild
	@cd deps/xed && ./mfile.py

%.o: %.c
	$(CC) $(CFLAGS) -c $<

clean:
	$(RM) *.o *.d testgen

depclean:
	$(RM) -r deps

-include *.d

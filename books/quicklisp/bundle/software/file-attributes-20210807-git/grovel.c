#include <sys/stat.h>
#include <stddef.h>
#include <stdio.h>

#define print_member(type, member)                                      \
  printf("\n  (%-10s :uint%i :offset %2i)", #member, 8 * sizeof(type.member), offsetof(struct type, member))

int main(){
  struct stat stat;
  printf("(cffi:defcstruct (%s :size %i)", "stat", sizeof(struct stat));
  print_member(stat, st_mode);
  print_member(stat, st_uid);
  print_member(stat, st_gid);
  print_member(stat, st_size);
  print_member(stat, st_atime);
  print_member(stat, st_mtime);
  printf(")\n");
  return 0;
}

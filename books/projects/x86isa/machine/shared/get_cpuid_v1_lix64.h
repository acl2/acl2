typedef struct {
  unsigned int EAX;
  unsigned int EBX;
  unsigned int ECX;
  unsigned int EDX;
} CPUIDinfo;

extern void get_cpuid_info_v1(CPUIDinfo *info, const unsigned int func, const unsigned int subfunc) asm("get_cpuid_info_v1");

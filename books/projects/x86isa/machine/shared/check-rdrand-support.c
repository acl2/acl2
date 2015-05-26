// Slightly modified by Shilpi Goel.
// Source:
// http://software.intel.com/en-us/articles/intel-digital-random-number-generator-drng-software-implementation-guide/

#include "stdio.h"
#include "string.h"
#include "get_cpuid_v1_lix64.h"

void CPUID(CPUIDinfo *info, const unsigned int func, const unsigned int subfunc)
{
	get_cpuid_info_v1(info, func, subfunc);
}

typedef unsigned int DWORD;

int rdrand_check_support()
{
  CPUIDinfo info;
  int got_intel_cpu=0;
  CPUID(&info,0,0);
  if(memcmp((char *)(&info.EBX), "Genu", 4) == 0 &&
     memcmp((char *)(&info.EDX), "ineI", 4) == 0 &&
     memcmp((char *)(&info.ECX), "ntel", 4) == 0) {
    got_intel_cpu = 1;
  }

  if (got_intel_cpu) {
    CPUID(&info,1,0);
    if ((info.ECX & 0x40000000)==0x40000000) return 1;
  }
  return 0;
}

int main () {
  return (rdrand_check_support());
}

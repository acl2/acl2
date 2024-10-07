// Copyright (C) 2023-2024 David S. Hardin
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.

// **** Circular Doubly-Linked List (CDLL) to support Knuth's "Dancing Links"
// **** Mainly automatically generated from the CDLL Rust code

#include <stddef.h>
#include <stdint.h>

#include <array>
#include <tuple>

using namespace std;

#include <ac_int.h>
#include <rac.h>

// RAC begin

typedef ac_int<1, true>   i1;
typedef ac_int<1, false>  u1;
typedef ac_int<2, true>   i2;
typedef ac_int<2, false>  u2;
typedef ac_int<3, true>   i3;
typedef ac_int<3, false>  u3;
typedef ac_int<4, true>   i4;
typedef ac_int<4, false>  u4;
typedef ac_int<5, true>   i5;
typedef ac_int<5, false>  u5;
typedef ac_int<6, true>   i6;
typedef ac_int<6, false>  u6;
typedef ac_int<7, true>   i7;
typedef ac_int<7, false>  u7;
typedef ac_int<8, true>   i8;
typedef ac_int<8, false>  u8;
typedef ac_int<9, true>   i9;
typedef ac_int<9, false>  u9;
typedef ac_int<10, true>   i10;
typedef ac_int<10, false>  u10;
typedef ac_int<11, true>   i11;
typedef ac_int<11, false>  u11;
typedef ac_int<12, true>   i12;
typedef ac_int<12, false>  u12;
typedef ac_int<13, true>   i13;
typedef ac_int<13, false>  u13;
typedef ac_int<14, true>   i14;
typedef ac_int<14, false>  u14;
typedef ac_int<15, true>   i15;
typedef ac_int<15, false>  u15;
typedef ac_int<16, true>   i16;
typedef ac_int<16, false>  u16;
typedef ac_int<17, true>   i17;
typedef ac_int<17, false>  u17;
typedef ac_int<18, true>   i18;
typedef ac_int<18, false>  u18;
typedef ac_int<19, true>   i19;
typedef ac_int<19, false>  u19;
typedef ac_int<20, true>   i20;
typedef ac_int<20, false>  u20;
typedef ac_int<21, true>   i21;
typedef ac_int<21, false>  u21;
typedef ac_int<22, true>   i22;
typedef ac_int<22, false>  u22;
typedef ac_int<23, true>   i23;
typedef ac_int<23, false>  u23;
typedef ac_int<24, true>   i24;
typedef ac_int<24, false>  u24;
typedef ac_int<25, true>   i25;
typedef ac_int<25, false>  u25;
typedef ac_int<26, true>   i26;
typedef ac_int<26, false>  u26;
typedef ac_int<27, true>   i27;
typedef ac_int<27, false>  u27;
typedef ac_int<28, true>   i28;
typedef ac_int<28, false>  u28;
typedef ac_int<29, true>   i29;
typedef ac_int<29, false>  u29;
typedef ac_int<30, true>   i30;
typedef ac_int<30, false>  u30;
typedef ac_int<31, true>   i31;
typedef ac_int<31, false>  u31;
typedef ac_int<32, true>   i32;
typedef ac_int<32, false>  u32;
typedef ac_int<33, true>   i33;
typedef ac_int<33, false>  u33;
typedef ac_int<34, true>   i34;
typedef ac_int<34, false>  u34;
typedef ac_int<35, true>   i35;
typedef ac_int<35, false>  u35;
typedef ac_int<36, true>   i36;
typedef ac_int<36, false>  u36;
typedef ac_int<37, true>   i37;
typedef ac_int<37, false>  u37;
typedef ac_int<38, true>   i38;
typedef ac_int<38, false>  u38;
typedef ac_int<39, true>   i39;
typedef ac_int<39, false>  u39;
typedef ac_int<40, true>   i40;
typedef ac_int<40, false>  u40;
typedef ac_int<41, true>   i41;
typedef ac_int<41, false>  u41;
typedef ac_int<42, true>   i42;
typedef ac_int<42, false>  u42;
typedef ac_int<43, true>   i43;
typedef ac_int<43, false>  u43;
typedef ac_int<44, true>   i44;
typedef ac_int<44, false>  u44;
typedef ac_int<45, true>   i45;
typedef ac_int<45, false>  u45;
typedef ac_int<46, true>   i46;
typedef ac_int<46, false>  u46;
typedef ac_int<47, true>   i47;
typedef ac_int<47, false>  u47;
typedef ac_int<48, true>   i48;
typedef ac_int<48, false>  u48;
typedef ac_int<49, true>   i49;
typedef ac_int<49, false>  u49;
typedef ac_int<50, true>   i50;
typedef ac_int<50, false>  u50;
typedef ac_int<51, true>   i51;
typedef ac_int<51, false>  u51;
typedef ac_int<52, true>   i52;
typedef ac_int<52, false>  u52;
typedef ac_int<53, true>   i53;
typedef ac_int<53, false>  u53;
typedef ac_int<54, true>   i54;
typedef ac_int<54, false>  u54;
typedef ac_int<55, true>   i55;
typedef ac_int<55, false>  u55;
typedef ac_int<56, true>   i56;
typedef ac_int<56, false>  u56;
typedef ac_int<57, true>   i57;
typedef ac_int<57, false>  u57;
typedef ac_int<58, true>   i58;
typedef ac_int<58, false>  u58;
typedef ac_int<59, true>   i59;
typedef ac_int<59, false>  u59;
typedef ac_int<60, true>   i60;
typedef ac_int<60, false>  u60;
typedef ac_int<61, true>   i61;
typedef ac_int<61, false>  u61;
typedef ac_int<62, true>   i62;
typedef ac_int<62, false>  u62;
typedef ac_int<63, true>   i63;
typedef ac_int<63, false>  u63;
typedef ac_int<64, true>   i64;
typedef ac_int<64, false>  u64;

typedef uint usize ;

const usize CDLL_EXP  = 13;
const usize CDLL_MSB  = CDLL_EXP - 1;
const usize CDLL_MAX_NODE1  = 8191;
const usize CDLL_MAX_NODE  = CDLL_MAX_NODE1 - 1;


struct CDLLNode {
  u2 alloc ;
  i64 val ;
  usize prev ;
  usize next ;
};


struct CDLL {
  usize nodeHd ;
  usize nodeCount ;
  array<CDLLNode, 8191> nodeArr ;
};




CDLL  CDLL_initNodes(    CDLL CDObj )         {
  CDObj.nodeArr[0].alloc = 2;
  CDObj.nodeArr[0].val = 0;
  CDObj.nodeArr[0].prev = 0;
  CDObj.nodeArr[0].next = 0;

   for (        usize i  = 1; i < CDLL_MAX_NODE1; i+=1) {
    CDObj.nodeArr[i].alloc = 2;
    CDObj.nodeArr[i].val = 0;
    CDObj.nodeArr[i].prev = i;
    CDObj.nodeArr[i].next = i;
  }  

  return CDObj;
}


CDLL  CDLL_initAll(    CDLL CDObj )         {
  CDObj.nodeHd = 0;
  CDObj.nodeCount = 0;
  CDObj = CDLL_initNodes(CDObj);

  return CDObj;
}


bool  CDLL_isEmpty(CDLL CDObj )         {
  return (CDObj.nodeCount == 0);
}


bool  CDLL_isFull(CDLL CDObj )         {
  return (CDObj.nodeCount == CDLL_MAX_NODE1);
}


usize  CDLL_sizeOf(CDLL CDObj )          {
  return (CDObj.nodeCount);
}


usize  CDLL_find_edge_index_for_node(usize nIndex , CDLL CDObj )          {
          usize i  = 0;
   for (i = 0; ((i < CDLL_MAX_NODE1) && ((CDObj.nodeArr[i].alloc == 2) || ((CDObj.nodeArr[i].prev != nIndex) && (CDObj.nodeArr[i].next != nIndex)))); i+=1) {
  }  

  return i;
}


usize  CDLL_find_free_node(usize ndCount , array<CDLLNode, 8191> arr)          {
  if (ndCount == CDLL_MAX_NODE1) {
    return CDLL_MAX_NODE1;
  } else {
            usize i  = 0;
     for (i = 0; ((i < CDLL_MAX_NODE1) && (arr[i].alloc != 2)); i+=1) {
    }  
    return i;
  }
}


CDLL  CDLL_add_node_at_index(usize index , i64 v ,     CDLL CDObj )         {
  if ((CDObj.nodeCount != CDLL_MAX_NODE1) && (v != -2 * 2147483648 * 2147483648)) {
    CDObj.nodeArr[index].alloc = 3;
    CDObj.nodeCount = CDObj.nodeCount + 1;
    CDObj.nodeArr[index].prev = index;      // loop to self initially
    CDObj.nodeArr[index].next = index;      // loop to self initially
    CDObj.nodeArr[index].val = v;
  }
  return CDObj;
}


CDLL  CDLL_add_node(i64 v ,     CDLL CDObj )         {
  if ((CDObj.nodeCount != CDLL_MAX_NODE1) && (v != -2 * 2147483648 * 2147483648)) {
        usize index  = CDLL_find_free_node(CDObj.nodeCount, CDObj.nodeArr);
    if (index < CDLL_MAX_NODE1) {
      CDObj.nodeArr[index].alloc = 3;
      CDObj.nodeCount = CDObj.nodeCount + 1;
      CDObj.nodeArr[index].prev = index;      // loop to self initially
      CDObj.nodeArr[index].next = index;      // loop to self initially
      CDObj.nodeArr[index].val = v;
    }
  }
  return CDObj;
}


CDLL  CDLL_delete_node_refs_from_edges(usize ndel ,     CDLL CDObj )         {
   for (        usize n  = CDLL_MAX_NODE1; n > 0; n-=1) {
    if (CDObj.nodeArr[n-1].prev == ndel) {
      CDObj.nodeArr[n-1].prev = n-1;
    }
    if (CDObj.nodeArr[n-1].next == ndel) {
      CDObj.nodeArr[n-1].next = n-1;
    }
  }  
  return CDObj;
}


CDLL  CDLL_delete_node(usize n ,     CDLL CDObj )         {
  if (CDObj.nodeCount > 0) {
    CDObj.nodeCount = (CDObj.nodeCount - 1);
  }
      usize lindex  = CDObj.nodeArr[n].prev;
      usize rindex  = CDObj.nodeArr[n].next;

  CDObj.nodeArr[n].alloc = 2;
//  CDObj.nodeArr[n].val = 0;
//  CDObj.nodeArr[n].prev = 0;
//  CDObj.nodeArr[n].next = 0;

  if (CDObj.nodeArr[lindex].next == n) {
    if (rindex == n) {  // Nothing next
      CDObj.nodeArr[lindex].next = lindex;
    } else {
      CDObj.nodeArr[lindex].next = rindex;
    }
  }
  if (CDObj.nodeArr[rindex].prev == n) {
    if (lindex == n) {  // Nothing previous
      CDObj.nodeArr[rindex].prev = rindex;
    } else {
      CDObj.nodeArr[rindex].prev = lindex;
    }
  }

  return CDObj;
}


CDLL  CDLL_delete_node_edge_scrub(usize n ,     CDLL CDObj )         {
  if (CDObj.nodeCount > 0) {
    CDObj.nodeCount = (CDObj.nodeCount - 1);
  }
  CDObj.nodeArr[n].alloc = 2;
//  CDObj.nodeArr[n].val = 0;
//  CDObj.nodeArr[n].prev = 0;
//  CDObj.nodeArr[n].next = 0;
  CDObj = CDLL_delete_node_refs_from_edges(n, CDObj);

  return CDObj;
}


CDLL  CDLL_change_edge_target(usize n , u1 edgenum , usize nnew ,     CDLL CDObj )         {
  if (n < CDLL_MAX_NODE1) {
    if (edgenum == 0) {
      CDObj.nodeArr[n].next = nnew;
    } else {
      CDObj.nodeArr[n].prev = nnew;
    }
  }
  return CDObj;
}


usize  CDLL_nthNodeBy(usize n , u1 edgenum ,     usize index , array<CDLLNode, 8191> arr)          {
   for (        usize i  = n; ((i > 0) && (index < CDLL_MAX_NODE1)); i-=1) {
    if (arr[index].alloc != 3) {
      index = CDLL_MAX_NODE1;
    } else {
      if (edgenum == 0) {
        index = arr[index].next;
      } else {
        index = arr[index].prev;
      }
    }
  }  

  if ((index < CDLL_MAX_NODE1) && (arr[index].alloc == 3)) {
    return index;
  } else {
    return CDLL_MAX_NODE1;
  }
}


usize  CDLL_findNodeBy(u1 edgenum , i64 datum ,     usize index , CDLL CDObj )          {
  if (datum == -2 * 2147483648 * 2147483648) {
    return CDLL_MAX_NODE1;
  } else {
            usize i  = 0;
     for (i = 0; ((i < CDLL_MAX_NODE1) && (CDObj.nodeArr[index].val != datum)); i+=1) {
       if (edgenum == 0) {
         index = CDObj.nodeArr[index].next;
       } else {
         index = CDObj.nodeArr[index].prev;
       }
     }  
     if (i == CDLL_MAX_NODE1) {
       return CDLL_MAX_NODE1;
     } else {
       return index;
     }
   }
}


usize  CDLL_depthOf(u1 edgenum , i64 datum ,     usize index , CDLL CDObj )          {
  if (datum == -2 * 2147483648 * 2147483648) {
    return CDLL_MAX_NODE1;
  } else {
            usize i  = CDObj.nodeCount+1;
    if (edgenum == 0) {
       for (i = CDObj.nodeCount+1; ((i > 0) && (CDObj.nodeArr[index].val != datum)); i-=1) {
        index = CDObj.nodeArr[index].next;
      }  
      return (CDObj.nodeCount - i);
    } else {
       for (i = CDObj.nodeCount+1; ((i > 0) && (CDObj.nodeArr[index].val != datum)); i-=1) {
        index = CDObj.nodeArr[index].prev;
      }  
      return (CDObj.nodeCount - i);
    }
  }
}


i64  CDLL_hd(CDLL CDObj )        {
  if (CDObj.nodeCount == 0) {
    return -2 * 2147483648 * 2147483648;
  } else {
    return CDObj.nodeArr[CDObj.nodeHd].val;
  }
}


i64  CDLL_tl(CDLL CDObj )        {
  if (CDObj.nodeCount == 0) {
    return -2 * 2147483648 * 2147483648;
  } else {
    return CDObj.nodeArr[CDObj.nodeArr[CDObj.nodeHd].prev].val;
  }
}


i64  CDLL_nth(usize j , CDLL CDObj )        {
  if ((CDObj.nodeCount == 0) || (j >= CDObj.nodeCount))  {
    return -2 * 2147483648 * 2147483648;
  } else {
    if (j == 0) {
      return CDObj.nodeArr[CDObj.nodeHd].val;
    } else {
          usize jthNode  = CDLL_nthNodeBy(j, 0, CDObj.nodeHd, CDObj.nodeArr);

      if (jthNode == CDLL_MAX_NODE1) {
        return -2 * 2147483648 * 2147483648;
      } else {
        return CDObj.nodeArr[jthNode].val;
      }
    }
  }
}


i64  CDLL_nth_prev(usize j , CDLL CDObj )        {
  if ((CDObj.nodeCount == 0) || (j >= CDObj.nodeCount))  {
    return -2 * 2147483648 * 2147483648;
  } else {
    if (j == 0) {
      return CDObj.nodeArr[CDObj.nodeHd].val;
    } else {
          usize jthNode  = CDLL_nthNodeBy(j, 1, CDObj.nodeHd, CDObj.nodeArr);

      if (jthNode == CDLL_MAX_NODE1) {
        return -2 * 2147483648 * 2147483648;
      } else {
        return CDObj.nodeArr[jthNode].val;
      }
    }
  }
}


usize  CDLL_ln(CDLL CDObj )          {
  return CDObj.nodeCount;
}


i64  CDLL_ln_count(CDLL CDObj )        {
          i64 lnc  = 0;
          usize nd  = CDObj.nodeHd;

  if (nd == CDObj.nodeArr[nd].next) {
    return lnc;
  } else {
    lnc = lnc + 1;
    nd = CDObj.nodeArr[nd].next;
            usize i  = CDLL_MAX_NODE1;
     for (i = CDLL_MAX_NODE1; ((i > 0) && (nd != CDObj.nodeHd)); i-=1) {
      lnc = lnc + 1;
      nd = CDObj.nodeArr[nd].next;
    }  

    if (i == 0) {
      lnc = -1;
    }
    return lnc;
  }
}


CDLL  CDLL_rst(    CDLL CDObj )         {
      usize hdIndex  = CDObj.nodeHd;
  if (CDObj.nodeCount == 0) {
    return CDObj;
  } else {
    if (CDObj.nodeCount == 1) {
      CDObj.nodeHd = 0;
    } else {
      CDObj.nodeHd = CDObj.nodeArr[hdIndex].next;

      if (CDObj.nodeCount == 2) {
        CDObj.nodeArr[CDObj.nodeHd].prev = CDObj.nodeHd;   // Loop
        CDObj.nodeArr[CDObj.nodeHd].next = CDObj.nodeHd;   // Loop
      } else {
        CDObj.nodeArr[CDObj.nodeHd].prev = CDObj.nodeArr[hdIndex].prev;   // Close the circle
      }
    }
    return CDLL_delete_node(hdIndex, CDObj);
  }
}


CDLL  CDLL_tsr(    CDLL CDObj )         {
      usize tlIndex  = CDObj.nodeArr[CDObj.nodeHd].prev;
  if (CDObj.nodeCount == 0) {
    return CDObj;
  } else {
    if (CDObj.nodeCount == 1) {
      CDObj.nodeHd = 0;
    } else {
      if (CDObj.nodeCount == 2) {
        CDObj.nodeArr[CDObj.nodeHd].prev = CDObj.nodeHd;   // Loop
        CDObj.nodeArr[CDObj.nodeHd].next = CDObj.nodeHd;   // Loop
      } else {
        CDObj.nodeArr[CDObj.nodeHd].prev = CDObj.nodeArr[tlIndex].prev;   // Close the circle
      }
    }
    return CDLL_delete_node(tlIndex, CDObj);
  }
}


// fn CDLL_del(j: usize, mut CDObj: CDLL) -> CDLL {
//   if (j >= CDObj.nodeCount) {
//     return CDObj;
//   } else {
//     if (j == 0) {
//       return CDLL_rst(CDObj);
//     } else {
//       if (j == (CDObj.nodeCount - 1)) {
//         return CDLL_tsr(CDObj);
//       } else {
//         let jthNode: usize = CDLL_nthNodeBy(j, 0, CDObj.nodeHd, CDObj.nodeArr);
//         let nextNode: usize = CDObj.nodeArr[jthNode].next;
//         let prevNode: usize = CDObj.nodeArr[jthNode].prev;

//         CDObj.nodeArr[prevNode].next = nextNode;
//         CDObj.nodeArr[nextNode].prev = prevNode;

//         return CDLL_delete_node(jthNode, CDObj);
//       }
//     }
//   }
// }


CDLL  CDLL_cns(i64 v ,     CDLL CDObj )         {
  if ((CDObj.nodeCount == CDLL_MAX_NODE1) || (v == -2 * 2147483648 * 2147483648)) {
    return CDObj;
  } else {
        usize index  = CDLL_find_free_node(CDObj.nodeCount, CDObj.nodeArr);

    if (index > CDLL_MAX_NODE) {
      return CDObj;
    } else {
      if ((CDObj.nodeCount > 0) &&
          ((CDObj.nodeHd > CDLL_MAX_NODE) || (CDObj.nodeArr[CDObj.nodeHd].alloc != 3))) {
        return CDObj;
      } else {
        if (CDObj.nodeCount > 0) {
              usize tl  = CDObj.nodeArr[CDObj.nodeHd].prev;
    
          CDObj.nodeArr[tl].next = index;                // Close the circle

          CDObj.nodeArr[index].next = CDObj.nodeHd;
          CDObj.nodeArr[CDObj.nodeHd].prev = index;

          CDObj.nodeArr[index].prev = tl;                // Close the circle
        } else {  // nodeCount == 0
          CDObj.nodeArr[index].prev = index;            // loop to self initially
          CDObj.nodeArr[index].next = index;            // loop to self initially
        }

        CDObj.nodeHd = index;
        CDObj.nodeArr[index].alloc = 3;
        CDObj.nodeCount = CDObj.nodeCount + 1;
        CDObj.nodeArr[index].val = v;

        return CDObj;
      }
    }
  }
}


// Cons after the head node

CDLL  CDLL_cns1(i64 v ,     CDLL CDObj )         {
  if ((CDObj.nodeCount == 0) || ((CDObj.nodeCount == CDLL_MAX_NODE1) ||
      (v == -2 * 2147483648 * 2147483648))) {
    return CDObj;
  } else {
        usize index  = CDLL_find_free_node(CDObj.nodeCount, CDObj.nodeArr);

    if (index > CDLL_MAX_NODE) {
      return CDObj;
    } else {
      if ((CDObj.nodeHd > CDLL_MAX_NODE) || (CDObj.nodeArr[CDObj.nodeHd].alloc != 3)) {
        return CDObj;
      } else {
        CDObj.nodeArr[index].next = CDObj.nodeArr[CDObj.nodeHd].next;

        CDObj.nodeArr[index].prev = CDObj.nodeHd;

        CDObj.nodeCount = CDObj.nodeCount + 1;
        CDObj.nodeArr[index].val = v;

        CDObj.nodeArr[index].alloc = 3;

        // Break nodeCount == 1 self-loop
        // if (CDObj.nodeCount == 1) {
        // if (CDObj.nodeArr[CDObj.nodeHd].prev == CDObj.nodeHd) {   
        //  CDObj.nodeArr[CDObj.nodeHd].prev = index;
        CDObj.nodeArr[CDObj.nodeArr[CDObj.nodeHd].next].prev = index;

        CDObj.nodeArr[CDObj.nodeHd].next = index;

        return CDObj;
      }
    }
  }
}


CDLL  CDLL_snc(i64 v ,     CDLL CDObj )         {
  if ((CDObj.nodeCount == CDLL_MAX_NODE1) || (v == -2 * 2147483648 * 2147483648)) {
    return CDObj;
   } else {
        usize index  = CDLL_find_free_node(CDObj.nodeCount, CDObj.nodeArr);

    if (index > CDLL_MAX_NODE) {
      return CDObj;
    } else {
      if ((CDObj.nodeCount > 0) &&
          ((CDObj.nodeHd > CDLL_MAX_NODE) || (CDObj.nodeArr[CDObj.nodeHd].alloc != 3))) {
        return CDObj;
      } else {
        if (CDObj.nodeCount > 0) {
              usize tl  = CDObj.nodeArr[CDObj.nodeHd].prev;

          CDObj.nodeArr[tl].next = index;
          CDObj.nodeArr[index].prev = tl;

          CDObj.nodeArr[index].next = CDObj.nodeHd;    // Close the circle
          CDObj.nodeArr[CDObj.nodeHd].prev = index;    // Close the circle
        } else {  // nodeCount == 0
          CDObj.nodeArr[index].prev = index;            // loop to self initially
          CDObj.nodeArr[index].next = index;            // loop to self initially

          CDObj.nodeHd = index;
        }

        CDObj.nodeArr[index].alloc = 3;
        CDObj.nodeCount = CDObj.nodeCount + 1;
        CDObj.nodeArr[index].val = v;

        return CDObj;
      }
    }
  }
}


CDLL  CDLL_ins(usize j , i64 v ,     CDLL CDObj )         {
  if ((j >= CDObj.nodeCount) ||
      ((CDObj.nodeCount == CDLL_MAX_NODE1) || (v == -2 * 2147483648 * 2147483648))) {
    return CDObj;
  } else {
    if (j >= CDObj.nodeCount) {
      return CDObj;
    } else {
      if (CDObj.nodeCount == 0) {
        return CDObj;
      } else {                                            // 0 < j < nodeCount
            usize jthNode  = CDLL_nthNodeBy(j, 0, CDObj.nodeHd, CDObj.nodeArr);

        if (jthNode == CDLL_MAX_NODE1) {
          return CDObj;
        } else {
              usize prevHd  = CDObj.nodeHd;
          CDObj.nodeHd = jthNode;

          CDObj = CDLL_cns1(v, CDObj);
          CDObj.nodeHd = prevHd;
            
          return CDObj;
        }
      }
    }
  }
}


CDLL  CDLL_del(usize j ,     CDLL CDObj )         {
  if ((j > CDObj.nodeCount) || (CDObj.nodeCount == 0)) {
    return CDObj;
  } else {
    if (j == 0) {
      return CDLL_rst(CDObj);
    } else {
      if ((j > 0) && (j == CDObj.nodeCount)) {
        return CDLL_tsr(CDObj);
      } else {                                            // 0 < j < nodeCount
            usize jthNode  = CDLL_nthNodeBy(j, 0, CDObj.nodeHd, CDObj.nodeArr);

        if (jthNode == CDLL_MAX_NODE) {
            return CDObj;
        } else {
          if (CDObj.nodeArr[jthNode].alloc != 3) {
              return CDObj;
            } else {

                usize prevHd  = CDObj.nodeHd;
            CDObj.nodeHd = jthNode;

            CDObj = CDLL_rst(CDObj);

            CDObj.nodeHd = prevHd;

            return CDObj;
          }
        }
      }
    }
  }
}


// Lighter-weight, "Dancing Links" version of del -- accepts raw index instead of position in list

CDLL  CDLL_remove(usize n ,     CDLL CDObj )         {
  if (n > CDLL_MAX_NODE) {
    return CDObj;
  } else {
    if (n == CDObj.nodeHd) {  // Can't remove head
      return CDObj;
    } else {
      if (CDObj.nodeCount < 3) {  // Need three elements for remove to work
        return CDObj;
      } else {
            usize nextNode  = CDObj.nodeArr[n].next;
            usize prevNode  = CDObj.nodeArr[n].prev;

        CDObj.nodeArr[prevNode].next = nextNode;
        CDObj.nodeArr[nextNode].prev = prevNode;

        CDObj.nodeCount = CDObj.nodeCount - 1;

        return CDObj;
      }
    }
  }
}


// Lighter-weight, "Dancing Links" version of ins -- accepts raw index instead of position in list

CDLL  CDLL_restore(usize n ,     CDLL CDObj )         {
  if (n > CDLL_MAX_NODE) {
    return CDObj;
  } else {
    if (n == CDObj.nodeHd) {  // Can't restore head
      return CDObj;
    } else {
      if ((CDObj.nodeCount < 2) ||         // Need two elements for restore to work
          (CDObj.nodeCount == CDLL_MAX_NODE1))  {    // Can't restore to a full list
        return CDObj;
      } else {

            usize prevNode  = CDObj.nodeArr[n].prev;
            usize nextNode  = CDObj.nodeArr[n].next;

        CDObj.nodeArr[prevNode].next = n;
        CDObj.nodeArr[nextNode].prev = n;

        CDObj.nodeCount = CDObj.nodeCount + 1;

        return CDObj;
      }
    }
  }
}

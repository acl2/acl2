// Copyright (C) 2023 David S. Hardin
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


type i1 = i8;  // oversized
type u1 = u8;
type i2 = i8;
type u2 = u8;
type i3 = i8;
type u3 = u8;
type i4 = i8;
type u4 = u8;
type i5 = i8;
type u5 = u8;
type i6 = i8;
type u6 = u8;
type i7 = i8;
type u7 = u8;
type i9 = i16;  // oversized
type u9 = u16;
type i10 = i16;
type u10 = u16;
type i11 = i16;
type u11 = u16;
type i12 = i16;
type u12 = u16;
type i13 = i16;
type u13 = u16;
type i14 = i16;
type u14 = u16;
type i15 = i16;
type u15 = u16;
type i17 = i32;  // oversized
type u17 = u32;
type i18 = i32;
type u18 = u32;
type i19 = i32;
type u19 = u32;
type i20 = i32;
type u20 = u32;
type i21 = i32;
type u21 = u32;
type i22 = i32;
type u22 = u32;
type i23 = i32;
type u23 = u32;
type i24 = i32;
type u24 = u32;
type i25 = i32;
type u25 = u32;
type i26 = i32;
type u26 = u32;
type i27 = i32;
type u27 = u32;
type i28 = i32;
type u28 = u32;
type i29 = i32;
type u29 = u32;
type i30 = i32;
type u30 = u32;
type i31 = i32;
type u31 = u32;
type i33 = i64;  // oversized
type u33 = u64;
type i34 = i64;
type u34 = u64;
type i35 = i64;
type u35 = u64;
type i36 = i64;
type u36 = u64;
type i37 = i64;
type u37 = u64;
type i38 = i64;
type u38 = u64;
type i39 = i64;
type u39 = u64;
type i40 = i64;
type u40 = u64;
type i41 = i64;
type u41 = u64;
type i42 = i64;
type u42 = u64;
type i43 = i64;
type u43 = u64;
type i44 = i64;
type u44 = u64;
type i45 = i64;
type u45 = u64;
type i46 = i64;
type u46 = u64;
type i47 = i64;
type u47 = u64;
type i48 = i64;
type u48 = u64;
type i49 = i64;
type u49 = u64;
type i50 = i64;
type u50 = u64;
type i51 = i64;
type u51 = u64;
type i52 = i64;
type u52 = u64;
type i53 = i64;
type u53 = u64;
type i54 = i64;
type u54 = u64;
type i55 = i64;
type u55 = u64;
type i56 = i64;
type u56 = u64;
type i57 = i64;
type u57 = u64;
type i58 = i64;
type u58 = u64;
type i59 = i64;
type u59 = u64;
type i60 = i64;
type u60 = u64;
type i61 = i64;
type u61 = u64;
type i62 = i64;
type u62 = u64;
type i63 = i64;
type u63 = u64;

const CDLL_EXP: usize = 13;
const CDLL_MSB: usize = CDLL_EXP - 1;
const CDLL_MAX_NODE1: usize = 8191;
const CDLL_MAX_NODE: usize = CDLL_MAX_NODE1 - 1;

#[derive(Copy, Clone)]
struct CDLLNode {
  alloc: u2,
  val: i64,
  prev: usize,
  next: usize,
}

#[derive(Copy, Clone)]
struct CDLL {
  nodeHd: usize,
  nodeCount: usize,
  nodeArr: [CDLLNode; 8191],
}


#[macro_use] extern crate cfor;

fn CDLL_initNodes(mut CDObj: CDLL) -> CDLL {
  CDObj.nodeArr[0].alloc = 2;
  CDObj.nodeArr[0].val = 0;
  CDObj.nodeArr[0].prev = 0;
  CDObj.nodeArr[0].next = 0;

  cfor!{let mut i: usize = 1; i < CDLL_MAX_NODE1; i+=1; {
    CDObj.nodeArr[i].alloc = 2;
    CDObj.nodeArr[i].val = 0;
    CDObj.nodeArr[i].prev = i;
    CDObj.nodeArr[i].next = i;
  } }

  return CDObj;
}


fn CDLL_initAll(mut CDObj: CDLL) -> CDLL {
  CDObj.nodeHd = 0;
  CDObj.nodeCount = 0;
  CDObj = CDLL_initNodes(CDObj);

  return CDObj;
}


fn CDLL_isEmpty(CDObj: CDLL) -> bool {
  return (CDObj.nodeCount == 0);
}


fn CDLL_isFull(CDObj: CDLL) -> bool {
  return (CDObj.nodeCount == CDLL_MAX_NODE1);
}


fn CDLL_sizeOf(CDObj: CDLL) -> usize {
  return (CDObj.nodeCount);
}


fn CDLL_find_edge_index_for_node(nIndex: usize, CDObj: CDLL) -> usize {
  let mut i: usize = 0;
  cfor!{; ((i < CDLL_MAX_NODE1) && ((CDObj.nodeArr[i].alloc == 2) || ((CDObj.nodeArr[i].prev != nIndex) && (CDObj.nodeArr[i].next != nIndex)))); i+=1; {
  } }

  return i;
}


fn CDLL_find_free_node(ndCount: usize, arr: &[CDLLNode]) -> usize {
  if (ndCount == CDLL_MAX_NODE1) {
    return CDLL_MAX_NODE1;
  } else {
    let mut i: usize = 0;
    cfor!{; ((i < CDLL_MAX_NODE1) && (arr[i].alloc != 2)); i+=1; {
    } }
    return i;
  }
}


fn CDLL_add_node_at_index(index: usize, v: i64, mut CDObj: CDLL) -> CDLL {
  if ((CDObj.nodeCount != CDLL_MAX_NODE1) && (v != -2 * 2147483648 * 2147483648)) {
    CDObj.nodeArr[index].alloc = 3;
    CDObj.nodeCount = CDObj.nodeCount + 1;
    CDObj.nodeArr[index].prev = index;      // loop to self initially
    CDObj.nodeArr[index].next = index;      // loop to self initially
    CDObj.nodeArr[index].val = v;
  }
  return CDObj;
}


fn CDLL_add_node(v: i64, mut CDObj: CDLL) -> CDLL {
  if ((CDObj.nodeCount != CDLL_MAX_NODE1) && (v != -2 * 2147483648 * 2147483648)) {
    let index: usize = CDLL_find_free_node(CDObj.nodeCount, &CDObj.nodeArr);
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


fn CDLL_delete_node_refs_from_edges(ndel: usize, mut CDObj: CDLL) -> CDLL {
  cfor!{let mut n: usize = CDLL_MAX_NODE1; n > 0; n-=1; {
    if (CDObj.nodeArr[n-1].prev == ndel) {
      CDObj.nodeArr[n-1].prev = n-1;
    }
    if (CDObj.nodeArr[n-1].next == ndel) {
      CDObj.nodeArr[n-1].next = n-1;
    }
  } }
  return CDObj;
}


fn CDLL_delete_node(n: usize, mut CDObj: CDLL) -> CDLL {
  if (CDObj.nodeCount > 0) {
    CDObj.nodeCount = (CDObj.nodeCount - 1);
  }
  let lindex: usize = CDObj.nodeArr[n].prev;
  let rindex: usize = CDObj.nodeArr[n].next;

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


fn CDLL_delete_node_edge_scrub(n: usize, mut CDObj: CDLL) -> CDLL {
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


fn CDLL_change_edge_target(n: usize, edgenum: u1, nnew: usize, mut CDObj: CDLL) -> CDLL {
  if (n < CDLL_MAX_NODE1) {
    if (edgenum == 0) {
      CDObj.nodeArr[n].next = nnew;
    } else {
      CDObj.nodeArr[n].prev = nnew;
    }
  }
  return CDObj;
}


fn CDLL_nthNodeBy(n: usize, edgenum: u1, mut index: usize, arr: &[CDLLNode]) -> usize {
  cfor!{let mut i: usize = n; ((i > 0) && (index < CDLL_MAX_NODE1)); i-=1; {
    if (arr[index].alloc != 3) {
      index = CDLL_MAX_NODE1;
    } else {
      if (edgenum == 0) {
        index = arr[index].next;
      } else {
        index = arr[index].prev;
      }
    }
  } }

  if ((index < CDLL_MAX_NODE1) && (arr[index].alloc == 3)) {
    return index;
  } else {
    return CDLL_MAX_NODE1;
  }
}


fn CDLL_findNodeBy(edgenum: u1, datum: i64, mut index: usize, CDObj: CDLL) -> usize {
  if (datum == -2 * 2147483648 * 2147483648) {
    return CDLL_MAX_NODE1;
  } else {
    let mut i: usize = 0;
    cfor!{; ((i < CDLL_MAX_NODE1) && (CDObj.nodeArr[index].val != datum)); i+=1; {
       if (edgenum == 0) {
         index = CDObj.nodeArr[index].next;
       } else {
         index = CDObj.nodeArr[index].prev;
       }
     } }
     if (i == CDLL_MAX_NODE1) {
       return CDLL_MAX_NODE1;
     } else {
       return index;
     }
   }
}


fn CDLL_depthOf(edgenum: u1, datum: i64, mut index: usize, CDObj: CDLL) -> usize {
  if (datum == -2 * 2147483648 * 2147483648) {
    return CDLL_MAX_NODE1;
  } else {
    let mut i: usize = CDObj.nodeCount+1;
    if (edgenum == 0) {
      cfor!{; ((i > 0) && (CDObj.nodeArr[index].val != datum)); i-=1; {
        index = CDObj.nodeArr[index].next;
      } }
      return (CDObj.nodeCount - i);
    } else {
      cfor!{; ((i > 0) && (CDObj.nodeArr[index].val != datum)); i-=1; {
        index = CDObj.nodeArr[index].prev;
      } }
      return (CDObj.nodeCount - i);
    }
  }
}


fn CDLL_hd(CDObj: CDLL) -> i64 {
  if (CDObj.nodeCount == 0) {
    return -2 * 2147483648 * 2147483648;
  } else {
    return CDObj.nodeArr[CDObj.nodeHd].val;
  }
}


fn CDLL_tl(CDObj: CDLL) -> i64 {
  if (CDObj.nodeCount == 0) {
    return -2 * 2147483648 * 2147483648;
  } else {
    return CDObj.nodeArr[CDObj.nodeArr[CDObj.nodeHd].prev].val;
  }
}


fn CDLL_nth(j: usize, CDObj: CDLL) -> i64 {
  if ((CDObj.nodeCount == 0) || (j >= CDObj.nodeCount))  {
    return -2 * 2147483648 * 2147483648;
  } else {
    if (j == 0) {
      return CDObj.nodeArr[CDObj.nodeHd].val;
    } else {
      let jthNode: usize = CDLL_nthNodeBy(j, 0, CDObj.nodeHd, &CDObj.nodeArr);

      if (jthNode == CDLL_MAX_NODE1) {
        return -2 * 2147483648 * 2147483648;
      } else {
        return CDObj.nodeArr[jthNode].val;
      }
    }
  }
}


fn CDLL_nth_prev(j: usize, CDObj: CDLL) -> i64 {
  if ((CDObj.nodeCount == 0) || (j >= CDObj.nodeCount))  {
    return -2 * 2147483648 * 2147483648;
  } else {
    if (j == 0) {
      return CDObj.nodeArr[CDObj.nodeHd].val;
    } else {
      let jthNode: usize = CDLL_nthNodeBy(j, 1, CDObj.nodeHd, &CDObj.nodeArr);

      if (jthNode == CDLL_MAX_NODE1) {
        return -2 * 2147483648 * 2147483648;
      } else {
        return CDObj.nodeArr[jthNode].val;
      }
    }
  }
}


fn CDLL_ln(CDObj: CDLL) -> usize {
  return CDObj.nodeCount;
}


fn CDLL_ln_count(CDObj: CDLL) -> i64 {
  let mut lnc: i64 = 0;
  let mut nd: usize = CDObj.nodeHd;

  if (nd == CDObj.nodeArr[nd].next) {
    return lnc;
  } else {
    lnc = lnc + 1;
    nd = CDObj.nodeArr[nd].next;
    let mut i: usize = CDLL_MAX_NODE1;
    cfor!{; ((i > 0) && (nd != CDObj.nodeHd)); i-=1; {
      lnc = lnc + 1;
      nd = CDObj.nodeArr[nd].next;
    } }

    if (i == 0) {
      lnc = -1;
    }
    return lnc;
  }
}


fn CDLL_rst(mut CDObj: CDLL) -> CDLL {
  let hdIndex: usize = CDObj.nodeHd;
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


fn CDLL_tsr(mut CDObj: CDLL) -> CDLL {
  let tlIndex: usize = CDObj.nodeArr[CDObj.nodeHd].prev;
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
//         let jthNode: usize = CDLL_nthNodeBy(j, 0, CDObj.nodeHd, &CDObj.nodeArr);
//         let nextNode: usize = CDObj.nodeArr[jthNode].next;
//         let prevNode: usize = CDObj.nodeArr[jthNode].prev;

//         CDObj.nodeArr[prevNode].next = nextNode;
//         CDObj.nodeArr[nextNode].prev = prevNode;

//         return CDLL_delete_node(jthNode, CDObj);
//       }
//     }
//   }
// }


fn CDLL_cns(v: i64, mut CDObj: CDLL) -> CDLL {
  if ((CDObj.nodeCount == CDLL_MAX_NODE1) || (v == -2 * 2147483648 * 2147483648)) {
    return CDObj;
  } else {
    let index: usize = CDLL_find_free_node(CDObj.nodeCount, &CDObj.nodeArr);

    if (index > CDLL_MAX_NODE) {
      return CDObj;
    } else {
      if ((CDObj.nodeCount > 0) &&
          ((CDObj.nodeHd > CDLL_MAX_NODE) || (CDObj.nodeArr[CDObj.nodeHd].alloc != 3))) {
        return CDObj;
      } else {
        if (CDObj.nodeCount > 0) {
          let tl: usize = CDObj.nodeArr[CDObj.nodeHd].prev;
    
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

fn CDLL_cns1(v: i64, mut CDObj: CDLL) -> CDLL {
  if ((CDObj.nodeCount == 0) || ((CDObj.nodeCount == CDLL_MAX_NODE1) ||
      (v == -2 * 2147483648 * 2147483648))) {
    return CDObj;
  } else {
    let index: usize = CDLL_find_free_node(CDObj.nodeCount, &CDObj.nodeArr);

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


fn CDLL_snc(v: i64, mut CDObj: CDLL) -> CDLL {
  if ((CDObj.nodeCount == CDLL_MAX_NODE1) || (v == -2 * 2147483648 * 2147483648)) {
    return CDObj;
   } else {
    let index: usize = CDLL_find_free_node(CDObj.nodeCount, &CDObj.nodeArr);

    if (index > CDLL_MAX_NODE) {
      return CDObj;
    } else {
      if ((CDObj.nodeCount > 0) &&
          ((CDObj.nodeHd > CDLL_MAX_NODE) || (CDObj.nodeArr[CDObj.nodeHd].alloc != 3))) {
        return CDObj;
      } else {
        if (CDObj.nodeCount > 0) {
          let tl: usize = CDObj.nodeArr[CDObj.nodeHd].prev;

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


fn CDLL_ins(j: usize, v: i64, mut CDObj: CDLL) -> CDLL {
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
        let jthNode: usize = CDLL_nthNodeBy(j, 0, CDObj.nodeHd, &CDObj.nodeArr);

        if (jthNode == CDLL_MAX_NODE1) {
          return CDObj;
        } else {
          let prevHd: usize = CDObj.nodeHd;
          CDObj.nodeHd = jthNode;

          CDObj = CDLL_cns1(v, CDObj);
          CDObj.nodeHd = prevHd;
            
          return CDObj;
        }
      }
    }
  }
}


fn CDLL_del(j: usize, mut CDObj: CDLL) -> CDLL {
  if ((j > CDObj.nodeCount) || (CDObj.nodeCount == 0)) {
    return CDObj;
  } else {
    if (j == 0) {
      return CDLL_rst(CDObj);
    } else {
      if ((j > 0) && (j == CDObj.nodeCount)) {
        return CDLL_tsr(CDObj);
      } else {                                            // 0 < j < nodeCount
        let jthNode: usize = CDLL_nthNodeBy(j, 0, CDObj.nodeHd, &CDObj.nodeArr);

        if (jthNode == CDLL_MAX_NODE) {
            return CDObj;
        } else {
          if (CDObj.nodeArr[jthNode].alloc != 3) {
              return CDObj;
            } else {

            let prevHd: usize = CDObj.nodeHd;
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

fn CDLL_remove(n: usize, mut CDObj: CDLL) -> CDLL {
  if (n > CDLL_MAX_NODE) {
    return CDObj;
  } else {
    if (n == CDObj.nodeHd) {  // Can't remove head
      return CDObj;
    } else {
      if (CDObj.nodeCount < 3) {  // Need three elements for remove to work
        return CDObj;
      } else {
        let nextNode: usize = CDObj.nodeArr[n].next;
        let prevNode: usize = CDObj.nodeArr[n].prev;

        CDObj.nodeArr[prevNode].next = nextNode;
        CDObj.nodeArr[nextNode].prev = prevNode;

        CDObj.nodeCount = CDObj.nodeCount - 1;

        return CDObj;
      }
    }
  }
}


// Lighter-weight, "Dancing Links" version of ins -- accepts raw index instead of position in list

fn CDLL_restore(n: usize, mut CDObj: CDLL) -> CDLL {
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

        let prevNode: usize = CDObj.nodeArr[n].prev;
        let nextNode: usize = CDObj.nodeArr[n].next;

        CDObj.nodeArr[prevNode].next = n;
        CDObj.nodeArr[nextNode].prev = n;

        CDObj.nodeCount = CDObj.nodeCount + 1;

        return CDObj;
      }
    }
  }
}


// Construct a new CDLL_Node

fn CDLLNode_construct() -> CDLLNode {
  CDLLNode {
    alloc: 2,
    val: 0,
    prev: 0,
    next: 0,
  }
}


// Construct a new CDLL

fn CDLL_construct() -> CDLL {
  CDLL {
    nodeHd: 0,
    nodeCount: 0,
    nodeArr: [CDLLNode_construct(); CDLL_MAX_NODE1],
  }
}


fn main() {
//  let mut dl: &mut CDLL = &mut CDLL { nodeTop: CDLL_MAX_SZ, nodeArr: [0; CDLL_MAX_SZ], };
  let dl: CDLL = CDLL_construct();

  let dl = CDLL_cns(4, dl);
//  println!("CDLL_ln() = {}", CDLL_ln(dl));
//  println!("CDLL_hd() = {}", CDLL_hd(dl));
//  println!("CDLL_tl() = {}", CDLL_tl(dl));
  let dl = CDLL_cns(3, dl);
//  println!("CDLL_ln() = {}", CDLL_ln(dl));
//  println!("CDLL_hd() = {}", CDLL_hd(dl));
//  println!("CDLL_tl() = {}", CDLL_tl(dl));
  let dl = CDLL_snc(5, dl);
//  println!("CDLL_ln() = {}", CDLL_ln(dl));
//  println!("CDLL_ln_count() = {}", CDLL_ln_count(dl));
  println!("CDLL_hd() = {}", CDLL_hd(dl));
  println!("CDLL_nth(1) = {}", CDLL_nth(1, dl));
  println!("CDLL_tl() = {}", CDLL_tl(dl));


  println!("INS(0,1):");

  let dl = CDLL_ins(0, 1, dl);

  println!("CDLL_nth(0) = {}", CDLL_nth(0, dl));
  println!("CDLL_nth(1) = {}", CDLL_nth(1, dl));
  println!("CDLL_nth(2) = {}", CDLL_nth(2, dl));
  println!("CDLL_tl = {}", CDLL_tl(dl));  
  println!("CDLL_ln() = {}", CDLL_ln(dl));

  println!("DEL(1):");

//  let dl = CDLL_ins(3, 2, dl);
  let dl = CDLL_del(1, dl);

  println!("CDLL_nth(0) = {}", CDLL_nth(0, dl));
  println!("CDLL_nth(1) = {}", CDLL_nth(1, dl));
  println!("CDLL_nth(2) = {}", CDLL_nth(2, dl));
//  println!("CDLL_nth(3) = {}", CDLL_nth(3, dl));
  println!("CDLL_tl = {}", CDLL_tl(dl));  
  println!("CDLL_ln() = {}", CDLL_ln(dl));

}

// fn main() {
// //  let mut dl: &mut CDLL = &mut CDLL { nodeTop: CDLL_MAX_SZ, nodeArr: [0; CDLL_MAX_SZ], };
//   let dl: CDLL = CDLL_construct();

//   let dl = CDLL_cns(3, dl);
//   println!("CDLL_ln() = {}", CDLL_ln(dl));
//   println!("CDLL_hd() = {}", CDLL_hd(dl));
//   println!("CDLL_tl() = {}", CDLL_tl(dl));
//   let dl = CDLL_cns(4, dl);
//   println!("CDLL_ln() = {}", CDLL_ln(dl));
//   println!("CDLL_hd() = {}", CDLL_hd(dl));
//   println!("CDLL_tl() = {}", CDLL_tl(dl));
//   let dl = CDLL_snc(5, dl);
// //  println!("CDLL_ln() = {}", CDLL_ln(dl));
//   println!("CDLL_ln_count() = {}", CDLL_ln_count(dl));
//   println!("CDLL_hd() = {}", CDLL_hd(dl));
//   println!("CDLL_tl() = {}", CDLL_tl(dl));


// // Insert dancing links example

//   println!("DANCING LINKS:");

//   println!("CDLL_nth(0) = {}", CDLL_nth(0, dl));
//   println!("CDLL_nth(1) = {}", CDLL_nth(1, dl));
//   println!("CDLL_nth(2) = {}", CDLL_nth(2, dl));

//   let n: usize = CDLL_nthNodeBy(1, 0, dl.nodeHd, &dl.nodeArr);
//   println!("n = {}", n);

//   let dl = CDLL_remove(n, dl);
//   println!("CDLL_hd = {}", CDLL_hd(dl));  
//   println!("CDLL_nth(1) = {}", CDLL_nth(1, dl));
//   println!("CDLL_tl = {}", CDLL_tl(dl));  

//   let dl = CDLL_restore(n, dl);
//   println!("CDLL_hd = {}", CDLL_hd(dl));  
//   println!("CDLL_nth(1) = {}", CDLL_nth(1, dl));
//   println!("CDLL_tl = {}", CDLL_tl(dl));  

//   println!("END DANCING LINKS");

// // End dancing links example

// //  let dl = CDLL_rst(dl);
// //  println!("CDLL_ln() = {}", CDLL_ln(dl));
// //  println!("CDLL_hd() = {}", CDLL_hd(dl));
// //  println!("CDLL_tl() = {}", CDLL_tl(dl));
// //  let dl = CDLL_tsr(dl);
// //  println!("CDLL_ln() = {}", CDLL_ln(dl));
// //  println!("CDLL_hd() = {}", CDLL_hd(dl));
// //  println!("CDLL_tl() = {}", CDLL_tl(dl));
// }

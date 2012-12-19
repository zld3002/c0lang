/* CC0 helper implementation
 *
 * Primitives used by the cc0 compiler that aren't specificed as part
 * of the cc0 runtime go here.
 * 
 * This header file uses c0runtime.h functions, but does not include
 * the c0runtime.h header because it does not know whether the runtime
 * has defined C0_RUNTIME_IMPELEMENTS_LENGTH or not.
 *
 * Interface: cc0/include/cc0lib.h
 */

#include <signal.h>
#include <c0runtime.h>
#include "cc0lib.h"

void c0_idiv_asn (int* px, int y) {
  *px = c0_idiv(*px, y);
}

void c0_imod_asn (int* px, int y) {
  *px = c0_imod(*px, y);
}

void c0_sal_asn (int* px, int y) {
  *px = c0_sal(*px, y);
}

void c0_sar_asn (int* px, int y) {
  *px = c0_sar(*px, y);
}

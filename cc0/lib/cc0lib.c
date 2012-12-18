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

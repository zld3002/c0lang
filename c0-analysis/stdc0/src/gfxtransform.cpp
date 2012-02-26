#include "gfx.h"
#include "gfxprivate.h"

// The QTransform APIs all take qreals so beware of the silent casting

STDC0API transform_t transform_create() {
  return new transform;
}

STDC0API transform_t transform_clone(transform_t t) {
  return new transform(*t);
}

STDC0API bool transform_can_invert(transform_t t) {
  return t->qtx.isInvertible();
}

STDC0API void transform_translate(transform_t t, int dx, int dy) {
  t->qtx.translate(dx, dy);
}

STDC0API void transform_rotate(transform_t t, int angle) {
  t->qtx.rotate(angle);
}

STDC0API void transform_scale(transform_t t, int xdenom, int xnum, int ydenom, int ynum) {
  t->qtx.scale(xnum/xdenom, ynum/ydenom);
}

STDC0API void transform_invert(transform_t t) {
  if (!transform_can_invert(t))
    return;
  t->qtx = t->qtx.inverted();
}

STDC0API path_t transform_path(transform_t t, path_t p) {
  return new path(t->qtx.map(p->qpath));
}

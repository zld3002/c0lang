#include "gfx.h"
#include "gfxprivate.h"

STDC0API pattern_t pattern_solid_color(int color) {
  return new pattern(color);
}

STDC0API pattern_t pattern_image(image_t i) {
  return new pattern(i->qimg);
}

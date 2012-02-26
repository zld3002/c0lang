#include "gfx.h"
#include "gfxprivate.h"

static const QImage::Format default_format = QImage::Format_ARGB32;

STDC0API image_t image_create(int width, int height) {
  return new image(QImage(width, height, default_format));
}

STDC0API image_t image_clone(image_t img) {
  return new image(img->qimg);
}

STDC0API image_t image_subimage(image_t img, int x, int y, int width, int height) {
  return new image(img->qimg.copy(x,y,width,height));
}

STDC0API image_t image_load(c0rt_string_t p) {
  c0rt::AutoCStr path(p);
  return new image(QImage(path.asQString()).convertToFormat(default_format));
}

STDC0API void image_save(image_t image, c0rt_string_t p) {
  c0rt::AutoCStr path(p);
  image->qimg.save(path.asQString());
}

STDC0API int image_width(image_t image) {
  return image->qimg.width();
}

STDC0API int image_height(image_t image) {
  return image->qimg.height();
}

STDC0API TYPED_ARRAY(int) image_data(image_t) {
  return (TYPED_ARRAY(int))c0rt_array_allocate(sizeof(int), 0);
}

STDC0API int image_getpixel(image_t image, int x, int y) {
  return image->qimg.pixel(x,y);
}

STDC0API void image_setpixel(image_t image, int x, int y, int value) {
  image->qimg.setPixel(x,y,value);
}

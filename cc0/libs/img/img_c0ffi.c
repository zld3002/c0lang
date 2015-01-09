/* img_c0ffi.c
 * This file automatically generated by the command 
 * 'wrappergen img' - editing is probably bad.
 * 
 * The call to wrappergen was likely probably by 
 * 'make libs/img', which in turn was likely
 * invoked by 'make libs'. */

#include <inttypes.h>
#include <c0runtime.h>

/* Headers */

struct image;
int image_width(struct image * image);
int image_height(struct image * image);
struct image * image_create(int width, int height);
struct image * image_clone(struct image * image);
struct image * image_subimage(struct image * image, int x, int y, int width, int height);
struct image * image_load(c0_string path);
void image_save(struct image * image, c0_string path);
c0_array * image_data(struct image * image);

/* Wrappers */

c0_value __c0ffi_image_width(c0_value *args) {
  return int2val(image_width((struct image *)val2ptr(args[0])));
}

c0_value __c0ffi_image_height(c0_value *args) {
  return int2val(image_height((struct image *)val2ptr(args[0])));
}

c0_value __c0ffi_image_create(c0_value *args) {
  return ptr2val((void *)image_create(val2int(args[0]), val2int(args[1])));
}

c0_value __c0ffi_image_clone(c0_value *args) {
  return ptr2val((void *)image_clone((struct image *)val2ptr(args[0])));
}

c0_value __c0ffi_image_subimage(c0_value *args) {
  return ptr2val((void *)image_subimage((struct image *)val2ptr(args[0]), val2int(args[1]), val2int(args[2]), val2int(args[3]), val2int(args[4])));
}

c0_value __c0ffi_image_load(c0_value *args) {
  return ptr2val((void *)image_load((c0_string)val2ptr(args[0])));
}

c0_value __c0ffi_image_save(c0_value *args) {
  image_save((struct image *)val2ptr(args[0]), (c0_string)val2ptr(args[1]));
  return ptr2val(NULL);
}

c0_value __c0ffi_image_data(c0_value *args) {
  return ptr2val((void *)image_data((struct image *)val2ptr(args[0])));
}


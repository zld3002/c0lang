/* PNG Image Library
 * Interface-compatible with old image library derived from Qt
 * This only handles PNG files
 * Author: Ben Chung
 * Translated from C++ to C: Frank Pfenning
 */
#include <c0runtime.h>
#include <stdio.h>
#include <png.h>
#include <assert.h>

/* accessing C0 arrays, usable as lvalue and rvalue */
#define sub(pixels, idx) *(int*)c0_array_sub(pixels, idx, sizeof(int))

struct image {
  int width;
  int height;
  c0_array pixels;
};
typedef struct image* image_t;

image_t image_create(int width, int height) {
  assert(0 < width && 0 < height);
  c0_array pixels = c0_array_alloc(sizeof(int), width*height);
  image_t image = c0_alloc(sizeof(struct image));
  image->width = width;
  image->height = height;
  image->pixels = pixels;
  return image;
}

image_t image_clone(image_t src) {
  assert(src != NULL);
  int width = src->width;
  int height = src->height;
  image_t dest = image_create(width, height);
  for (int i = 0; i < width*height; i++)
    sub(dest->pixels, i) = sub(src->pixels, i);
  return dest;
}

int image_width(image_t image) {
  assert(image != NULL);
  return image->width;
}

int image_height(image_t image) {
  assert(image != NULL);
  return image->height;
}

c0_array image_data(image_t image) {
  assert(image != NULL);
  return image->pixels;
}

/* for backward compatibility */
void image_destroy(image_t image) {
  return;
}

void image_to_png_bytes(png_bytep* dest, image_t src) {
  int width = src->width;
  int height = src->height;
  c0_array pixels = src->pixels;
  for (int i = 0; i < height; i++) {
    dest[i] = c0_alloc(sizeof(png_byte)*4*width);
    for (int x = 0; x < width; x++) {
      dest[i][x*4+0] = (char)((sub(pixels, x+i*width) & 0x00FF0000)>>16);
      dest[i][x*4+1] = (char)((sub(pixels, x+i*width) & 0x0000FF00)>>8);
      dest[i][x*4+2] = (char)((sub(pixels, x+i*width) & 0x000000FF)>>0);
      dest[i][x*4+3] = (char)((sub(pixels, x+i*width) & 0xFF000000)>>24);
    }
  }
}

void rgba_parse(png_bytep* row_pointers, image_t image) {
  int width = image->width;
  int height = image->height;
  c0_array pixels = image->pixels;
  for (int y = 0; y < height; y++) {
    png_byte* row = row_pointers[y];
    for (int x = 0; x < width; x++) {
      png_byte* ptr = &(row[x*4]);
      sub(pixels, x+y*width) =
	(ptr[3]<<24)|(ptr[0]<<16)|(ptr[1]<<8)|(ptr[2]<<0);
    }
  }
}

void rgb_parse(png_bytep* row_pointers, image_t image) {
  int width = image->width;
  int height = image->height;
  c0_array pixels = image->pixels;
  for (int y = 0; y < height; y++) {
    png_byte* row = row_pointers[y];
    for (int x = 0; x < width; x++) {
      png_byte* ptr = &(row[x*3]);
      sub(pixels, x+y*width) =
	(0xFF<<24)|(ptr[0]<<16)|(ptr[1]<<8)|(ptr[2]<<0);
    }
  }
}

image_t image_load(c0_string path) {
  const char* filename = c0_string_tocstr(path);
  FILE * read = fopen(filename, "r");
  if (!read) {
    /* cannot read file; return NULL */
    return NULL;
  }

  unsigned char sig[8];

  fread(sig, 1, 8, read);
  if (png_sig_cmp(sig, 0, 8)) {
    /* invalid image file; abort */
    c0_abort("Invalid image file");
  }

  png_structp png_ptr = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
  if (!png_ptr) {
    c0_abort("png internal error: creation of the png read structure failed");
  }

  png_infop info_ptr = png_create_info_struct(png_ptr);
  if (!info_ptr) {
    png_destroy_read_struct(&png_ptr, (png_infopp)NULL, (png_infopp)NULL);
    c0_abort("png internal error: creation of the png info structre failed");
  }

  png_infop end_info = png_create_info_struct(png_ptr);
  if (!end_info) {
    png_destroy_read_struct(&png_ptr, &end_info, (png_infopp)NULL);
    c0_abort("png internal error: failed to create end info struct");
  }

  if (setjmp(png_jmpbuf(png_ptr))) {
    png_destroy_read_struct(&png_ptr, &info_ptr, &end_info);
    fclose(read);
    fprintf(stderr, "png internal error: failed to open image '%s'\n",  filename);
    c0_abort("");
  }

  png_init_io(png_ptr, read);
  png_set_sig_bytes(png_ptr, 8);
  png_read_info(png_ptr, info_ptr);

  int width = png_get_image_width(png_ptr, info_ptr);
  int height = png_get_image_height(png_ptr, info_ptr);
  png_byte color_type = png_get_color_type(png_ptr, info_ptr);
  png_byte bit_depth = png_get_bit_depth(png_ptr, info_ptr);

  int number_of_passes = png_set_interlace_handling(png_ptr);
  png_read_update_info(png_ptr, info_ptr);
 
  png_bytep* row_pointers = c0_alloc(sizeof(png_bytep)*height);
  for (int y = 0; y < height; y++)
    row_pointers[y] = c0_alloc(sizeof(png_bytep)*png_get_rowbytes(png_ptr, info_ptr));
  png_read_image(png_ptr, row_pointers);
  fclose(read);

  image_t image = image_create(width, height);

  switch (color_type) {
  case PNG_COLOR_TYPE_RGB_ALPHA:
    rgba_parse(row_pointers, image);
    break;
  case PNG_COLOR_TYPE_RGB:
    rgb_parse(row_pointers, image);
    break;
  }
  png_destroy_read_struct(&png_ptr, &info_ptr, &end_info);

  return image;
}

image_t image_subimage(image_t src, int x, int y, int width, int height) {
  assert(src != NULL);
  image_t dest = image_create(width, height);
  for (int i = x; i < width+x; i++)
    for (int j = y; j < height+y; j++)
      if (0 <= i && i < src->width && 0 <= j && j < src->height)
	sub(dest->pixels, (i-x)+(j-y)*width) = sub(src->pixels, i+j*src->width);
      else
	sub(dest->pixels, (i-x)+(j-y)*width) = 0; /* may be redundant */
  return dest;
}

void image_save(image_t image, c0_string path) {
  const char* filename = c0_string_tocstr(path);

  int width = image->width;
  int height = image->height;
  c0_array pixels = image->pixels;

  FILE * fp = fopen(filename, "wb");
  if (fp == NULL) {
    c0_abort("Couldn't open output file");
  }

  png_structp png_ptr = png_create_write_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
  if (png_ptr == NULL) {
    fclose(fp);
    c0_abort("png internal error: creation of png write structure failed");
  }

  png_infop info_ptr = png_create_info_struct(png_ptr);
  if (info_ptr == NULL) {
    fclose(fp);
    c0_abort("png internal error: creation of the png info structure failed");
  }

  png_init_io(png_ptr, fp);

  if (setjmp(png_jmpbuf(png_ptr))) {
    fclose(fp);
    c0_abort("internal error: write IO failed unexpectedly");
  }

  png_set_IHDR(png_ptr, info_ptr, width, height, 8, 6,
	       PNG_INTERLACE_NONE, PNG_COMPRESSION_TYPE_BASE, PNG_FILTER_TYPE_BASE);

  png_write_info(png_ptr, info_ptr);
  png_bytep* img_data = c0_alloc(sizeof(png_bytep)*height);
  image_to_png_bytes(img_data, image);
  png_write_image(png_ptr, img_data);
  png_write_end(png_ptr, NULL);

  png_destroy_write_struct(&png_ptr, &info_ptr);
  fclose(fp);
  return;
}

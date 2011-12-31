#include <c0runtime.h>
#include <stdio.h>
#include <png.h>

//Originally created by Frank Pfenning - Modified to use libpng by Ben Chung
// Stash in an anonymous namespace to avoid name collisions
namespace {

class image : public c0::gcobject, public c0::safe<image> {
public:
  image(int width, int height)
  {
    this->width = width;
    this->height = height;
    pixels = new int[width*height];
  }
  image(const image &other)
  {
    width = other.width;
    height = other.height;
    pixels = new int[other.width*other.height];
    *pixels = *other.pixels;
  }

  image(c0::string filename)
  {
    //Covnert string using filename.qstr()
    LoadImage(filename.cstr());
  }

  ~image() 
  {
    delete pixels;
  }

  image *sub(int x, int y, int width, int height) {
    flushC0Array();
    image* output = new image(width, height);
    for (int i = x; i < this->width+x; i++)
      for (int j = y; j < this->height+y; j++)
	output->pixels[i-x+(j-y)*width] = pixels[i+j*this->width];
    return output;
  }

  void save(c0::string path) {
    flushC0Array();
    SaveImage(path.cstr());
  }

  int Width() const { return width; }
  int Height() const { return height; }

  c0::array<int> &bits() {
    if (!mArray) {
      mArray.initialize(width * height);
      for (int y = 0; y < height; y++) {
        for (int x = 0; x < width; x++) {
          mArray[y*width+x] = pixels[y*width+x];
        }
      }
    }
    return mArray;
  }

  void flushC0Array() {
    if (!mArray)
      return;
    for (int y = 0; y < height; y++) {
      for (int x = 0; x < width; x++) {
        pixels[y*width + x] = mArray[y*width+x];
      }
    }
  }

private:
  void LoadImage(const char* path)
  {
    FILE * read = fopen(path, "r");
    if (!read)
      c0_abort("Invalid file");

    unsigned char sig[8];

    fread(sig, 1, 8, read);
    if (png_sig_cmp(sig, 0, 8))
      c0_abort("Invalid image file");

    png_structp png_ptr = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
    if (!png_ptr)
       c0_abort("internal error - report as \"the creation of the png read structre failed\"");

    png_infop info_ptr = png_create_info_struct(png_ptr);
    if (!info_ptr)
      {
	png_destroy_read_struct(&png_ptr, (png_infopp)NULL, (png_infopp)NULL);
        c0_abort("internal error - report as \"the creation of the png info structre failed\"");
	return;
      }
    png_infop end_info = png_create_info_struct(png_ptr);
    if (!end_info)
      {
	png_destroy_read_struct(&png_ptr, &end_info, (png_infopp)NULL);
        c0_abort("internal error - report as \"Failed to create end info struct\"");
	return;
      }
    if (setjmp(png_jmpbuf(png_ptr)))
      {
	png_destroy_read_struct(&png_ptr, &info_ptr, &end_info);
	fclose(read);
        c0_abort("internal error - report as \"Error initalizing IO\"");
	return;
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
 
    png_bytep* row_pointers = new png_bytep[height];
    for (int y = 0; y < height; y++)
      row_pointers[y] = new png_byte[png_get_rowbytes(png_ptr, info_ptr)];
    png_read_image(png_ptr, row_pointers);
    fclose(read);

    int* output = new int[width*height];

    switch (color_type)
      {
      case PNG_COLOR_TYPE_RGB_ALPHA:
	RGBA_Parse(width, height, row_pointers, output);
	break;
      case PNG_COLOR_TYPE_RGB:
	RGB_Parse(width, height, row_pointers, output);
	break;
      }
    for (int i = 0; i < height; i++)
      delete (row_pointers[i]);
    delete (row_pointers);
    this->width = width;
    this->height = height;
    this->pixels = output;
    
  }

  void intarr_to_png_bytes(png_byte** output)
  {
    for (int i = 0; i < height; i++)
      {
	output[i] = new png_byte[4*width];
	for (int x = 0; x < width; x++)
	  {
	    output[i][x*4] = (char)((pixels[x+i*width] & 0x00FF0000)>>16);
	    output[i][x*4+1]=(char)((pixels[x+i*width] & 0x0000FF00)>>8);
	    output[i][x*4+2]=(char)((pixels[x+i*width] & 0x000000FF));
	    output[i][x*4+3]=(char)((pixels[x+i*width] & 0xFF000000)>>24);
	  }
      }
  }

  void cleanup_png_datarr(png_byte** row_pointers)
  {
    for (int i = 0; i < height; i++)
      {
	delete (row_pointers[i]);
      }
    delete (row_pointers);
  }
  void SaveImage(const char* name)
  {
    FILE * fp;
    png_structp png_ptr;
    png_infop info_ptr;

    fp = fopen(name, "wb");

    if (fp == NULL)
      c0_abort("The output file wan unable to be created");
    png_ptr = png_create_write_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
    if (png_ptr == NULL)
      {
	fclose(fp);
        c0_abort("internal error - report as \"the creation of the png write structre failed\"");
	return;
      }
    info_ptr = png_create_info_struct(png_ptr);
    if (info_ptr == NULL)
      {
	fclose(fp);
        c0_abort("internal error - report as \"the creation of the png info structre failed\"");
	png_destroy_write_struct(&png_ptr, (png_infopp)NULL);
	return;
      }
    png_init_io(png_ptr, fp);
    if (setjmp(png_jmpbuf(png_ptr)))
      {
	fclose(fp);
        c0_abort("internal error - report as \"a error in the write IO occured\"");
	png_destroy_write_struct(&png_ptr, (png_infopp)NULL);
	return;
      }

    png_set_IHDR(png_ptr, info_ptr, width, height, 8, 6, PNG_INTERLACE_NONE, PNG_COMPRESSION_TYPE_BASE, PNG_FILTER_TYPE_BASE);
    png_write_info(png_ptr, info_ptr);
    png_byte** imgData;
    imgData = new png_byte*[height];
    intarr_to_png_bytes(imgData);
    png_write_image(png_ptr, imgData);
    png_write_end(png_ptr, NULL);
    cleanup_png_datarr(imgData);
    fclose(fp);

  }

  void RGBA_Parse(int width, int height, png_bytep* row_pointers, int* output)
  {
    for (int y = 0; y < height; y++)
      {
	png_byte* row = row_pointers[y];
	for (int x = 0; x < width; x++)
	  {
	    png_byte* ptr = &(row[x*4]);
	    output[x+y*width] = (ptr[3]<<24)|(ptr[0] << 16)|(ptr[1] << 8)|(ptr[2]);
	  }
      }
  }
  void RGB_Parse(int width, int height, png_bytep* row_pointers, int* output)
  {
    for (int y = 0; y < height; y++)
      {
	png_byte* row = row_pointers[y];
	for (int x = 0; x < width; x++)
	  {
	    png_byte* ptr = &(row[x*3]);
	    output[x+y*width] = (255<<24)|(ptr[0]<<16)|(ptr[1] << 8)|(ptr[2]);
	  }
      }
  }
  int* pixels;
  int width, height;
  // Only valid if bits has been called
  c0::array<int> mArray;
};
}

C0API image* image_create(int width, int height) {
  if (width <= 0 || height <= 0)
    c0_abort("Image dimensions must be positive");
  return new image(width, height);
}

C0API image* image_clone(image *img) {
  img->flushC0Array();
  return new image(*img);
}

C0API void image_destroy(image* img) {
  img->destroy();
}

C0API image* image_subimage(image *img, int x, int y, int width, int height) {
  return img->sub(x, y, width, height);
}

C0API image* image_load(c0_string path) {
  return new image(path);
}

C0API void image_save(image *img, c0_string path) {
  img->save(path);
}

C0API int image_width(image* img) {
  return img->Width();
}

C0API int image_height(image* img) {
  return img->Height();
}

C0API c0_array *image_data(image* img) {
  return img->bits();
}

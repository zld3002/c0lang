#include <QImage>
#include <c0runtime.h>
#include <stdio.h>

// This is a thin wrapper around QImage. Access to the data is provided by
// copying to a c0_array. This data is then copied back before saving to disk
// or copying to another image.

// Stash in an anonymous namespace to avoid name collisions
namespace {
const QImage::Format default_format = QImage::Format_ARGB32;

class image : public c0::gcobject, public c0::safe<image> {
public:
  image(int width, int height)
    : mImage(width, height, default_format)
  {
    // Initialize to transparent black
    mImage.fill(0);
  }
  image(const image &other)
    : mImage(other.mImage)
  {}
  image(const QImage &img)
    : mImage(img)
  {}

  image(c0::string filename)
    : mImage(filename.qstr())
  {
    if (mImage.format() != default_format)
      mImage = mImage.convertToFormat(default_format);
  }

  image *sub(int x, int y, int width, int height) {
    flushC0Array();
    return new image(mImage.copy(x, y, width, height));
  }

  void save(c0::string path) {
    flushC0Array();
    if (!mImage.save(path.qstr()))
      c0_abort("Could not save image");
  }

  int width() const { return mImage.width(); }
  int height() const { return mImage.height(); }

  c0::array<int> &bits() {
    if (!mArray) {
      mArray.initialize(width() * height());
      for (int y = 0; y < height(); y++) {
        unsigned int *line = reinterpret_cast<unsigned int*>(mImage.scanLine(y));
        for (int x = 0; x < width(); x++) {
          mArray[y*width()+x] = line[x];
        }
      }
    }
    return mArray;
  }

  void flushC0Array() {
    if (!mArray)
      return;
    for (int y = 0; y < height(); y++) {
      unsigned int *line = reinterpret_cast<unsigned int*>(mImage.scanLine(y));
      for (int x = 0; x < width(); x++) {
        line[x] = mArray[y*width()+x];
      }
    }
  }

private:
  QImage mImage;
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
  img->validate();
  img->flushC0Array();
  return new image(*img);
}

C0API void image_destroy(image* img) {
  img->validate();
  img->destroy();
}

C0API image* image_subimage(image *img, int x, int y, int width, int height) {
  img->validate();
  return img->sub(x, y, width, height);
}

C0API image* image_load(c0_string path) {
  return new image(path);
}

C0API void image_save(image *img, c0_string path) {
  img->validate();
  img->save(path);
}

C0API int image_width(image* img) {
  img->validate();
  return img->width();
}

C0API int image_height(image* img) {
  img->validate();
  return img->height();
}

C0API c0_array *image_data(image* img) {
  img->validate();
  return img->bits();
}

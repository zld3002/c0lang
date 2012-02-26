#ifndef __STDC0GFX_H__
#define __STDC0GFX_H__

#include <limits.h>
#include "apidefs.h"

typedef struct path* path_t;

// Paths
// A path is a sequence of path segments. A path segment is a sequence of two
// dimensional points connected by line and/or curves.

// Creates a new path
STDC0API path_t path_create();
// Copies an existing path
STDC0API path_t path_clone(path_t path);
// Creates a new path that contains a rectangle given by x, y, width and height
STDC0API path_t path_rectangle(int x, int y, int width, int height);

// Creates a new empty path segment starting at the point (x,y)
STDC0API void path_move_to(path_t path, int x, int y);
// Adds a line from the end of the current path segment to (x,y)
STDC0API void path_line_to(path_t path, int x, int y);
// Adds a curve with control points (c1x,c1y) and (c2x,c2y) starting at the end
// of the current path segment and ending at (endx,endy)
STDC0API void path_cubic_to(path_t path,
                            int c1x, int c1y,
                            int c2x, int c2y,
                            int endx, int endy);
// Adds a curve with a control point (cx,cy) starting at the end of the current
// path segment and ending at (endx,endy)
STDC0API void path_quad_to(path_t path, int cx, int cy, int endx, int endy);

// Adds a new path segment in the shape of a rectangle with dimensions
// (width,height) at position (x,y).
STDC0API void path_add_rectangle(path_t path,
                                 int x, int y, int width, int height);
// Adds a new path segment in the shape of an ellipse with top left corner
// (x,y) and diameters width and height along the x and y axes respectively.
STDC0API void path_add_ellipse(path_t path,
                               int x, int y, int width, int height);

// Appends the path segments of the second path to the first
STDC0API void path_add_path(path_t path, path_t p);

// Translates all the points in the path by (dx,dy)
STDC0API void path_translate(path_t path, int dx, int dy);

#ifndef _cnaught
typedef enum {
  PATH_FILL_ODD_EVEN = 0,
  PATH_FILL_WINDING = 1,
  // Ensure that this enum has the same size as int
  PATH_FILL_SIZE = INT_MAX
} path_fill_rule;
#else // !defined(_cnaught)
typedef int path_fill_rule;
#endif // !defined(_cnaught)

// Sets the rule used to determine the shape that the path represents.
// The default rule is PATH_FILL_ODD_EVEN.
STDC0API void path_set_fill_rule(path_t path, path_fill_rule rule);

// Returns the sum of the lengths of each path segment in the path
STDC0API int path_length(path_t path);

// Returns whether or not the path contains the point (x,y) according to the
// the path's fill rule.
STDC0API bool path_contains_point(path_t path, int x, int y);

// Returns whether or not the path fully contains the rectangle given by
// (x,y,width,height) according to the path's fill rule.
STDC0API bool path_contains_rect(path_t path,
                                 int x, int y, int width, int height);

// Returns true if the given rectangle (x,y,width,height) intersects the path
// according to its fill rule. Returns false otherwise.
STDC0API bool path_intersects_rect(path_t path,
                                   int x, int y, int width, int height);

// Returns whether or not the two paths intersect according to their respective
// fill rules.
STDC0API bool path_intersects_path(path_t path, path_t p);

// Images
typedef struct image* image_t;

// Creates an ARGB image with dimensions (width,height)
STDC0API image_t image_create(int width, int height);

// Copies an existing image
STDC0API image_t image_clone(image_t image);

// Returns a copy of a subrectangle of the given image. The new image has
// dimensions (width,height). If part of the given rectangle is not contained
// within the given image, those pixels are assumed to be black.
STDC0API image_t image_subimage(image_t image, int x, int y, int width, int height);

// Loads an image from the given path and convert it if need be to an ARGB image
STDC0API image_t image_load(c0rt_string_t path);
// Saves the given image to disk, inferring the file type from the file
// extension given in the path.
STDC0API void image_save(image_t image, c0rt_string_t path);

// Retrieves the width of the given image.
STDC0API int image_width(image_t image);
// Retrieves the height of the given image.
STDC0API int image_height(image_t image);

// Returns a copy of the bits in the image
STDC0API TYPED_ARRAY(int) image_data(image_t image);

// Returns the pixel data at (x,y). Pixel data is packed into a single 32 bit
// integer. The individual channels are packed as 0xAARRGGBB
STDC0API int image_getpixel(image_t image, int x, int y);

// Sets the pixel data at (x,y) to the integer value which is assuemd to be in
// the same format as provided by image_getpixel (i.e. 0xAARRGGBB).
STDC0API void image_setpixel(image_t image, int x, int y, int value);

// Transformations
typedef struct transform* transform_t;

// Creates an identity transform
STDC0API transform_t transform_create();

// Copies an existing transform
STDC0API transform_t transform_clone(transform_t t);

// Returns true if the given transformation can be inverted
STDC0API bool transform_can_invert(transform_t t);

// Multiplies the transform with one tha translates by (dx,dy)
STDC0API void transform_translate(transform_t t, int dx, int dy);

// Multiplies the transform with one that rotates by the given number of degrees
STDC0API void transform_rotate(transform_t t, int degrees);

// Multiplies the transform with one that scales by (xnum/xdenom, ynum/ydenom).
// The transform is undefined if xdenom or ydenom are 0.
STDC0API void transform_scale(transform_t t, int xdenom, int xnum, int ydenom, int ynum);

// Does an in-place inversion of the transformation
STDC0API void transform_invert(transform_t t);

// Applies the transformation to a path, returning a new path
STDC0API path_t transform_path(transform_t t, path_t path);

// A pattern describes a source for drawing
typedef struct pattern* pattern_t;

// Creates a pattern that describes a solid color
STDC0API pattern_t pattern_solid_color(int color);

// Creates a pattern that describes an image
STDC0API pattern_t pattern_image(image_t i);

// TODO: add linear and radial gradiants

// A drawing context provides operations for drawing on an abstract surface
// without the user needing to know what type of surface is being used.

// A context consists of a clipping region, a transformation, a font, a fill
// pattern and a stroke pattern.
// Defaults:
//   clip region - the entire surface
//   transformation - the identity transformation
//   font - undefined (XXX: change this to 12pt sans serif)
//   fill pattern - undefined (XXX: change this to solid black)
//   stroke pattern - undefined (XXX: change this to solid black)
typedef struct context* context_t;

// Creates a context from an image.
STDC0API context_t context_from_image(image_t i);

// Notifies the context that the user is done drawing. Any subsequent drawing
// operations on this context are undefined.
STDC0API void context_finish(context_t c);

// Sets the clipping region of the context. All drawing operations are
// restricted to the area defined by the clip region.
STDC0API void context_clip(context_t c, path_t p);

// Strokes the given path using the context's stroke pattern
STDC0API void context_stroke_path(context_t c, path_t p);

// Fills in the given path using the context's fill pattern and the path's fill
// rule.
STDC0API void context_fill_path(context_t c, path_t p);

// Draws the given image at (x,y).
STDC0API void context_draw_image(context_t c, int x, int y, image_t i);

// Sets the current transformation of the context. This transform is applied to
// all drawing operations
STDC0API void context_set_transform(context_t c, transform_t t);

// Sets the context's font to the given family (ex: sans-serif, Arial, Minion,
// etc...) and size (expressed in points).
STDC0API void context_set_font(context_t c, c0rt_string_t family, int size);

// Draws text with the baseline of the first character starting at (x,y)
STDC0API void context_draw_text(context_t c, int x, int y, c0rt_string_t text);

// Returns the width of the text as it would be drawn with the context's font
STDC0API int context_mesaure_text_width(context_t c, c0rt_string_t text);

// Returns the height of the text as it would be drawn with the context's font
STDC0API int context_mesaure_text_height(context_t c, c0rt_string_t text);

// Sets the context's fill pattern
STDC0API void context_set_fill_pattern(context_t c, pattern_t p);

// Sets the context's stroke pattern using the given width as the width of the
// stroke.
STDC0API void context_set_stroke_pattern(context_t c, pattern_t p, int width);

#endif

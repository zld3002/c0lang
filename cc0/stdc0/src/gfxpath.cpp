#include "gfx.h"
#include "gfxprivate.h"
#include <QPointF>
#include <QRectF>

// The QPainterPath APIs all take qreals so beware of the silent casting

// Path construction
STDC0API path_t path_create() {
  return new path;
}

STDC0API path_t path_clone(path_t path) {
  path_t p = path_create();
  p->qpath = path->qpath;
  return p;
}

STDC0API path_t path_rectangle(int x, int y, int width, int height) {
  path_t path = path_create();
  path_add_rectangle(path, x, y, width, height);
  return path;
}

STDC0API void path_move_to(path_t path, int x, int y) {
  path->qpath.moveTo(x, y);
}

STDC0API void path_line_to(path_t path, int x, int y) {
  path->qpath.lineTo(x,y);
}

STDC0API void path_cubic_to(path_t path,
                            int c1x, int c1y,
                            int c2x, int c2y,
                            int endx, int endy) {
  path->qpath.cubicTo(c1x, c1y, c2x, c2y, endx, endy);
}


STDC0API void path_quad_to(path_t path, int cx, int cy, int endx, int endy) {
  path->qpath.quadTo(cx, cy, endx, endy);
}

STDC0API void path_add_rectangle(path_t path,
                                 int x, int y, int width, int height) {
  path->qpath.addRect(x, y, width, height);
}

STDC0API void path_add_ellipse(path_t path,
                               int x, int y, int width, int height) {
  path->qpath.addEllipse(x, y, width, height);
}

STDC0API void path_add_path(path_t path, path_t p) {
  path->qpath.addPath(p->qpath);
}

// Path manipulation
STDC0API void path_translate(path_t path, int dx, int dy) {
  path->qpath.translate(dx, dy);
}

STDC0API void path_set_fill_rule(path_t path, path_fill_rule rule) {
  Qt::FillRule qrule;
  switch (rule) {
    default:
    case PATH_FILL_ODD_EVEN:
      qrule = Qt::OddEvenFill;
      break;
    case PATH_FILL_WINDING:
      qrule = Qt::WindingFill;
      break;
  }
  path->qpath.setFillRule(qrule);
}

// Path queries
STDC0API int path_length(path_t path) {
  return path->qpath.length();
}

STDC0API bool path_contains_point(path_t path, int x, int y) {
  return path->qpath.contains(QPointF(x,y));
}

STDC0API bool path_contains_rect(path_t path,
                                 int x, int y, int width, int height) {
  return path->qpath.contains(QRectF(x,y,width,height));
}

STDC0API bool path_intersects_rect(path_t path,
                                   int x, int y, int width, int height) {
  return path->qpath.intersects(QRectF(x,y,width,height));
}

STDC0API bool path_intersects_path(path_t path, path_t p) {
  return path->qpath.intersects(p->qpath);
}

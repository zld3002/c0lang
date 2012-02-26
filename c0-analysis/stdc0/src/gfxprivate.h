#ifndef __STDC0GFXPRIVATE_H__
#define __STDC0GFXPRIVATE_H__

#include <QPainterPath>
#include <QImage>
#include <QBrush>
#include <QPainter>
#include "apidefs.h"
#include "gfx.h"

struct path : public gc_cleanup {
  QPainterPath qpath;

  path() {}
  path(const QPainterPath &path) : qpath(path) {}
};

struct image : public gc_cleanup {
  QImage qimg;

  image() {}
  image(const QImage &i) : qimg(i) {}
};

struct transform : public gc_cleanup {
  QTransform qtx;
};

struct pattern : public gc_cleanup {
  QBrush qbrush;

  pattern(int color) : qbrush(QColor(color)) {}
  pattern(const QImage &i) : qbrush(i) {}
};

struct context : public gc_cleanup {
  QPainter qpainter;
  QBrush fillBrush;

  context(QPaintDevice *dev) : qpainter(dev) {}
};

#endif // __STDC0GFXPRIVATE_H__

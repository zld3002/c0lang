#include "gfx.h"
#include "gfxprivate.h"

STDC0API context_t context_from_image(image_t i) {
  return new context(&i->qimg);
}

STDC0API void context_finish(context_t c) {
  if (c->qpainter.isActive())
    c->qpainter.end();
}

STDC0API void context_clip(context_t c, path_t p) {
  c->qpainter.setClipping(!p->qpath.isEmpty());
  c->qpainter.setClipPath(p->qpath);
}

STDC0API void context_stroke_path(context_t c, path_t p) {
  c->qpainter.drawPath(p->qpath);
}

STDC0API void context_fill_path(context_t c, path_t p) {
  c->qpainter.fillPath(p->qpath, c->fillBrush);
}

STDC0API void context_draw_image(context_t c, int x, int y, image_t i) {
  c->qpainter.drawImage(QPoint(x,y), i->qimg);
}

STDC0API void context_set_transform(context_t c, transform_t t) {
  c->qpainter.setTransform(t->qtx);
}

STDC0API void context_set_font(context_t c, c0rt_string_t family, int size) {
  QFont f(c0rt::AutoCStr(family), size);
  c->qpainter.setFont(f);
}

STDC0API void context_draw_text(context_t c, int x, int y, c0rt_string_t text) {
  c->qpainter.drawText(x,y,c0rt::AutoCStr(text));
}

static QRectF context_measure_text(context_t c, c0rt_string_t text) {
  QRectF initialBounds(0, 0, 0, 0);
  QRectF measuredBounds;
  return c->qpainter.boundingRect(initialBounds, Qt::AlignLeft | Qt::TextSingleLine, c0rt::AutoCStr(text));
}

STDC0API int context_mesaure_text_width(context_t c, c0rt_string_t text) {
  return context_measure_text(c,text).width();
}

STDC0API int context_mesaure_text_height(context_t c, c0rt_string_t text) {
  return context_measure_text(c,text).height();
}

STDC0API void context_set_fill_pattern(context_t c, pattern_t p) {
  c->fillBrush = p->qbrush;
}

STDC0API void context_set_stroke_pattern(context_t c, pattern_t p, int width) {
  QPen pen(p->qbrush, width);
  c->qpainter.setPen(pen);
}


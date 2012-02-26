#ifndef __STDC0GUIPRIVATE_H__
#define __STDC0GUIPRIVATE_H__
#include <QWidget>
#include <QPainter>
#include <QResizeEvent>
#include <QMouseEvent>

#include "gui.h"
#include "gfxprivate.h"

#define SAFE_DISPATCH(evt, ...) if (mCallbacks && mCallbacks->evt) mCallbacks->evt(mUserContext, __VA_ARGS__)

struct window : public QWidget {
private:
  Q_OBJECT
public:
  window() :
    QWidget(NULL),
    mUserContext(NULL),
    mCallbacks(NULL)
  {
  }
protected:
  void paintEvent(QPaintEvent *e) {
    QWidget::paintEvent(e);

    context_t c = new context(this);
    SAFE_DISPATCH(paint, c);
    context_finish(c);
  }

  void resizeEvent(QResizeEvent *e) {
    int width = e->size().width();
    int height = e->size().height();

    SAFE_DISPATCH(resize, width, height);
  }

  void mouseDownEvent(QMouseEvent *e) {
    SAFE_DISPATCH(mouse_down, e->x(), e->y());
  }

  void mouseUpEvent(QMouseEvent *e) {
    SAFE_DISPATCH(mouse_up, e->x(), e->y());
  }

  void mouseMoveEvent(QMouseEvent *e) {
    SAFE_DISPATCH(mouse_move, e->x(), e->y());
  }

  // XXX These should really be private for good style but this definition
  // isn't public.
public:
  window_context_t mUserContext;
  window_callbacks *mCallbacks;
};

#endif // __STDC0GUIPRIVATE_H__

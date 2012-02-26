#include "apidefs.h"
#include "timer.h"
#include <QTimer>

class TimeData : public QObject {
Q_OBJECT
public:
  TimeData(timer_callback *cb, timer_context_t ctx) :
    QObject(NULL),
    mCallback(cb),
    mContext(ctx) {
  }
public slots:
  void fire() {
    if (mCallback)
      (*mCallback)(mContext);
  }
public:
  timer_callback *mCallback;
  timer_context_t mContext;
};

struct timer : public gc {
  QTimer qtimer;
  TimeData data;
  timer(timer_callback *cb, timer_context_t ctx) :
    data(cb, ctx) {
    QObject::connect(&qtimer, SIGNAL(timeout()), &data, SLOT(fire()));
  }
};


stdc0_timer_t timer_singleshot(int msec, timer_callback *cb, timer_context_t ctx) {
  stdc0_timer_t t = new timer(cb, ctx);
  t->qtimer.setInterval(msec);
  t->qtimer.setSingleShot(true);
  return t;
}

stdc0_timer_t timer_repeating(int msec, timer_callback *cb, timer_context_t ctx) {
  stdc0_timer_t t = new timer(cb, ctx);
  t->qtimer.setInterval(msec);
  return t;
}

STDC0API void timer_set_context(stdc0_timer_t t, timer_context_t ctx) {
  t->data.mContext = ctx;
}

STDC0API void timer_set_interval(stdc0_timer_t t, int msec) {
  t->qtimer.setInterval(msec);
}

STDC0API void timer_start(stdc0_timer_t t) {
  t->qtimer.start();
}

STDC0API void timer_stop(stdc0_timer_t t) {
  t->qtimer.stop();
}

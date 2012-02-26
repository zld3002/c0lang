#ifndef __STDC0TIMER_H__
#define __STDC0TIMER_H__

#include "apidefs.h"

#ifndef _cnaught

/* The type of a timer */
typedef struct timer* stdc0_timer_t;

struct timer_context;
typedef struct timer_context *timer_context_t;

typedef void (*timer_callback)(timer_context_t ctx);

/** @brief Creates a timer that fires once
 *
 * @param msec The delay before the timer is fired
 * @param cb The function the timer will invoke when fired
 * @param ctx The user-defined context passed to the callback function
 */
STDC0API stdc0_timer_t timer_singleshot(int msec, timer_callback *cb, timer_context_t ctx);

/** @brief Creates a timer that fires at a given interval
 *
 * @param msec The timer firing interval
 * @param cb The function the timer will invoke when fired
 * @param ctx The user-defined context passed to the callback function
 */
STDC0API stdc0_timer_t timer_repeating(int msec, timer_callback *cb, timer_context_t ctx);

/** @brief Changes the user-defined context that the timer passes to its
 * callback function.
 */
STDC0API void timer_set_context(stdc0_timer_t t, timer_context_t ctx);

// Changes the interval that the timer uses. If the timer is active, this change
// may not take effect until after it next fires.
STDC0API void timer_set_interval(stdc0_timer_t t, int msec);

// Starts the timer. If the timer is already started, this has no effect.
STDC0API void timer_start(stdc0_timer_t t);

// Stops the timer from firing.
STDC0API void timer_stop(stdc0_timer_t t);

#endif // !defined(_cnaught)

#endif // __STDC0TIMER_H__

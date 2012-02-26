#ifndef __STDC0AUDIO_H__
#define __STDC0AUDIO_H__

#include "apidefs.h"

struct audio_buffer_desc {
  // The number of channels in the audio stream - typically 1 or 2
  int channels;
  // The frequency expressed in samples per second. Must not be negative.
  int frequency;
  // True if the provided array only uses the lower 8 bits for sample data
  // If false, assumes 16 bit samples
  bool samples_are_8bit;
};

typedef struct audio_buffer_desc audio_buffer_desc;

typedef struct audio_clip audio_clip_t;

// Creats an audio clip from the given buffer description and an array of samples
STDC0API audio_clip_t audio_clip_create(audio_buffer_desc *desc, TYPED_ARRAY(int) samples);

// Plays an audio clip on the default sound device
STDC0API void audio_clip_play(audio_clip_t *clip);

// Retrieves the buffer description of an audio clip
STDC0API audio_buffer_desc *audio_clip_desc(audio_clip_t *clip);

// Retrieves the samples from the audio clip
STDC0API TYPED_ARRAY(int) audio_clip_samples(audio_clip_t *clip);

// Loads an audio clip from disk
STDC0API audio_clip_t audio_clip_load(c0rt_string_t filename);

// Saves an audio clip to disk in a .WAV format
STDC0API void audio_clip_save(audio_clip_t *clip, c0rt_string_t filename);

#endif // __STDC0AUDIO_H__


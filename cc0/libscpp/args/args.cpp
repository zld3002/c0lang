#include <vector>
#include <string.h>
#include <c0runtime.h>
#include <parse.h>

// CC0lib defines these
extern "C" int c0_argc;
extern "C" char **c0_argv;

namespace {

struct flag;
struct option;

flag *gFlags = NULL;
option *gOpts = NULL;

struct flag : public c0::gcobject {
  c0::string name;
  bool *ptr;
  flag *next;

  flag(c0_string name, bool *ptr)
    : name(name), ptr(ptr), next(gFlags)
  {
    gFlags = this;
  }
};

struct option : public c0::gcobject {
  c0::string name;
  option *next;

  option(c0::string name)
    : name(name), next(gOpts)
  {
    gOpts = this;
  }

  virtual void set(c0_string value) = 0;
};

struct string_option : public option {
  c0_string *ptr;

  string_option(c0::string name, c0_string *ptr)
    : option(name), ptr(ptr)
  {}

  void set(c0_string value) {
    *ptr = value;
  }
};

struct int_option : public option {
  int *ptr;

  int_option(c0::string name, int *ptr)
    : option(name), ptr(ptr)
  {}

  void set(c0_string value) {
    int *result = parse_int(value, 10);
    if (result != NULL)
      *ptr = *result;
    // TODO: handle error
    // (currently just doesn't set the value, but consumes the args -wjl)
  }
};

flag *get_flag(const char *name) {
  flag *f = gFlags;
  while (f && strcmp(f->name, name)) {
    f = f->next;
  }
  return f;
}

option *get_option(const char *name) {
  option *o = gOpts;
  while (o && strcmp(o->name, name)) {
    o = o->next;
  }
  return o;
}

}

C0API void args_flag(c0_string name, bool *value) {
  new flag(name, value);
}

C0API void args_int(c0_string name, int *value) {
  new int_option(name, value);
}

C0API void args_string(c0_string name, c0_string *value) {
  new string_option(name, value);
}

struct args {
  int argc;
  c0_array* argv;
};

C0API struct args* args_parse() {
  int argc = c0_argc - 1;
  char **argv = c0_argv+1;
  std::vector<const char *> args;
  for (; argc > 0; argv++, argc--) {
    flag *f = get_flag(*argv);
    if (f) {
      *f->ptr = true;
      continue;
    }

    option *o = get_option(*argv);
    if (o) {
      argc--;
      argv++;

      if (argc == 0)
        c0_abort("Expected argument but didn't find one");
      o->set(c0_string_fromliteral(*argv));
      continue;
    }
    args.push_back(*argv);
  }

  c0::array<c0_string> arr(args.size());
  for (int i = 0; i < args.size(); i++) {
    arr[i] = c0_string_fromliteral(args[i]);
  }

  struct args *res = (struct args *) c0_alloc(sizeof(struct args));
  res->argc = args.size();
  res->argv = arr;

  return res;
}

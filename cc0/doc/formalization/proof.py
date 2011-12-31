sections = []

class section(object):
  name = ''
  classes = []
  rulesets = []
  shownrulesets = []
  def __init__(self, name, shortname):
    self.name = name
    self.shortname = shortname
    self.classes = []
    self.rulesets = []
    self.shownrulesets = []
    global currentsection
    currentsection = self
    sections.append(self)
    #self.currentruleset = ruleset('', lambda s='': s)

  def showruleset(self, rs):
    self.shownrulesets.append(rs)

  def emit(self):
    if self.name:
      emit(r"\newcommand{\section%sdefs}{" % self.shortname)
      if self.classes:
        emit(klass.prolog)
        for i, c in enumerate(self.classes):
          c.emit()
          emitln()
        emit(klass.epilog)
      emit(r"}\newcommand{\section%srules}{" % self.shortname)

      emit(r'\begin{mathpar}')
      for rs in self.shownrulesets:
        emit(cmd(rs.name+"default"))
        emitln()
      emit(r'\end{mathpar}')
      emit(r"}\newcommand{\section%sruledefs}{" % self.shortname)
      for rs in self.shownrulesets:
        rs.emitrules()
      emit("}")

commands = []
def cmd(name, *args, **kwargs):
  opts = kwargs['opts'] if 'opts' in kwargs else None
  text = r"""\%(name)s""" % { "name": name } \
       + ("[%s]" % (opts,) if opts is not None else "") \
       + "".join("{%s}" % arg for arg in args)
  if len(args) == 0 and name != "tau":
    text += "{}"
  return text

class define(object):
  name = ''
  _nargs = 0
  varargs = False
  def __init__(self, name, fn, varargs=False, nomath=False):
    commands.append(self)
    self.name = name
    self.fn = fn
    self._nargs = fn.func_code.co_argcount
    self.varargs = varargs
    self.nomath = nomath

  @property
  def nargs(self):
    nargs = self._nargs
    if self.varargs:
      nargs += 1
    return nargs

  def __call__(self, *args, **kwargs):
    if self.varargs:
      posargs = list(args[0:self._nargs])
      remainingargs = args[self._nargs:]
      if remainingargs:
        posargs.append(','.join(map(str,remainingargs)))
      return cmd(self.name, *posargs, **kwargs)
    else:
      return cmd(self.name, *args, **kwargs)
  def emit(self):
    for c in commands:
      self.fn.func_globals[c.name] = c

    args = list("#%d" % (d+1) for d in range(self.nargs))
    prefix = r"""\newcommand{\%s}""" % self.name
    argcount = "[%d]" % self.nargs if self.nargs > 0 else ""
    if self.nomath:
      body = "{%s}" % self.fn(*args)
    else:
      body = r"{\ensuremath{%s}}" % self.fn(*args)
    text = prefix + argcount + body
    emit(text)
  def __str__(self):
    return self()

class builtin(define):
  def __init__(self, name):
    define.__init__(self, name, lambda: """""")
  def emit(self):
    pass

builtins = [
  "inferrule",
  "kw",
  "boxed",
  "OR",
  "ensuremath"
]

for b in builtins:
  builtin(b)

class klass(object):
  name = ""
  members = [[]]
  newlines = True
  def __init__(self, name, newlines=True):
    currentsection.classes.append(self)
    self.name = name
    self.members = [[]]
    self.newlines = newlines
    define("class" + name.strip('\\'), lambda: self.wrappedDefinition)
    define("class" + name.strip('\\') + "data", lambda: self.definition, nomath=True)
  def member(self, text, newline=None):
    self.members[-1].append(text)
    if (newline is None and self.newlines) or newline:
      self.members.append([])
    return self
  prolog = r"""\begin{tabular}{lrl}"""
  epilog = r"""\end{tabular}"""
  @property
  def wrappedDefinition(self):
    return klass.prolog + self.definition + klass.epilog
  @property
  def definition(self):
    members = list(self.members)
    if not members:
      members = [""]
    defn = ""
    for i,m in enumerate(members):
      args = r" \OR ".join(map(str,m))
      if i == 0:
        defn += "%s" % cmd("startdef", self.name, args)
      else:
        if args:
          defn += "%s" % cmd("contdef", args)
    return defn

  def emit(self):
    emit(self.definition)

# Global dictionary of all rulesets
# ruleset name -> ruleset
rulesets = {}

class ruleset(object):
  def __init__(self, name, fn):
    self.name = name
    self.fn = fn
  def specialize(self, prefix, kwargs={}):
    return Ruleset(self.name, self.fn, kwargs, prefix)

class RulesetDefinedExn(Exception):
  def __init__(self, name):
    self.name = name

class ManualClosure(object):
  def __init__(self, fn, env):
    self.fn = fn
    self.env = env

  def rebind(self, **env):
    self.env.update(env)

  def __str__(self):
    return self.fn(**self.env)

class Ruleset(define):
  section = None
  rules = []
  def __init__(self, name, fn, env, prefix=''):
    currentsection.currentruleset = self
    # If we've been defined before, don't init
    if hasattr(self,'fn'):
      return
    define.__init__(self, "rule"+prefix+name, fn)
    rulesets[self.name] = self
    currentsection.rulesets.append(self)
    self.section = currentsection
    self.friendlyname = name
    self.rules = []
    self.env = env
    self.fn.func_globals.update(env)
    rule("default")
  def __new__(cls, name, fn, env, prefix=''):
    name = 'rule'+prefix+name
    if name in rulesets:
      return rulesets[name]
    return super(Ruleset, cls).__new__(cls)

  def __call__(self, *args, **kwargs):
    env = dict()
    for i, arg in enumerate(self.fn.func_code.co_varnames):
      if i < len(args):
        env[arg] = args[i]
      else:
        env[arg] = self.env[arg]
    env.update(kwargs)
    return ManualClosure(self.fn, env)
  def __str__(self):
    return str(self())
  def __enter__(self):
    self.oldruleset = currentsection.currentruleset
    currentsection.currentruleset = self
  def __exit__(self, *args):
    currentsection.currentruleset = self.oldruleset
    del self.oldruleset
  def rule(self, name):
    for rule in self.rules:
      if rule.name == name:
        return rule
  def add(self, rule):
    self.rules.append(rule)
    return define(self.name + rule.name, lambda: rule.rule)
  def show(self):
    self.section.showruleset(self)
  def emitrules(self):
    emit(cmd("boxed", cmd(self.name+"defaultconclusion")))
    if not self.rules:
      emitln()
      return
    emitln()
    emit(r'\begin{mathpar}')
    for i, r in enumerate(self.rules[1:]):
      r.emit()
      emitln()
      # HAX
      if i in (14,34):
        emit(r"\end{mathpar}\begin{mathpar}")
    emit(r'\end{mathpar}')

class Premise(object):
  rule = None
  def __init__(self, rule):
    self.rule = rule
  def __call__(self, premise):
    if isinstance(premise, int):
      return self.rule.premises[premise]
    else:
      self.rule.premises.append(premise)
      premisesuffix = chr(ord('a')+len(self.rule.premises)-1)
      define(self.rule.macro.name + "premise"+premisesuffix, lambda: str(premise))
      return self.rule
  def __str__(self):
    return self.rule.premises[0]

class rule(object):
  name = ''
  premises = []
  conclusion = ''
  def __init__(self, name, ruleset=None, **kwargs):
    self.name = name
    self.ruleset = ruleset or currentsection.currentruleset
    self.premises = []
    self.conclusion = self.ruleset(**kwargs)
    self.premise = Premise(self)
    self.macro = self.ruleset.add(self)
    define(self.macro.name+"conclusion", lambda: str(self.conclusion))
    define(self.macro.name+"name", lambda: self.friendlyname, nomath=True)
    define(self.macro.name+"named", lambda: self.getrule(True))

  @property
  def friendlyname(self):
    return "%s-%s" % (self.ruleset.friendlyname, self.name)

  def getrule(self, usename):
    return builtin('inferrule*')(r" \\ ".join(map(str, self.premises)) or " ", self.conclusion, opts="right=%s" % builtin(self.macro.name+"name")() if usename else None) \

  @property
  def rule(self):
    return self.getrule(False)

  def __str__(self):
    return self.rule
  def emit(self):
    emit(builtin(self.ruleset.name + self.name)())

def emit(text=None):
  if text is not None:
    print text
    return
  for c in commands:
    c.emit()
  for s in sections:
    s.emit()

def emitln():
  emit("")

currentSection = section('','emptysection')
builtins = [
  "inferrule",
  "kw",
  "boxed",
  "OR"
]

for b in builtins:
  builtin(b)

__all__ = ["define", "klass", "emit", "rule", "ruleset", "builtin", "cmd", "section", "rulesets", "RulesetDefinedExn"]

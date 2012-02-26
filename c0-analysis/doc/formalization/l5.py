from proof import *

section("Definitions", "defs")

def callFuncWith(*args, **kwargs):
  fn = args[0]
  args = args[1:]
  old_globals = dict(fn.func_globals)
  fn.func_globals.update(kwargs)
  result = fn(*args)
  fn.func_globals.update(old_globals)
  return result

def specialize(prefix, env, *args):
  return tuple(globals()[rule].specialize(prefix, env) for rule in args)

def getPrefixedRuleset(rule, prefix, **kwargs):
  fn = globals()[rule+'rule']
  return callFuncWith(fn, prefix, **kwargs)

builtin("rightarrow")
builtin("in")
cdot = builtin("cdot")
ldots = builtin("ldots")
bot = builtin("bot")

amp = lambda a,b: "%s\ \&\ %s" % (a,b)
bar = lambda a,b: "%s\ \mid{} %s" % (a,b)
colon = lambda a,b: "%s : %s" % (a,b)
comma = lambda *args: ",".join(map(str,args))
semi = lambda *args: ';'.join(map(str,args))
entails = lambda a,b: r"%s \entails %s" % (a,b)
contains = lambda x,A: r"%s \in %s" % (x,A)
doesnotcontain = lambda x, G: r"%s \not\in %s" % (x,G)
equals = lambda a,b: "%s=%s" % (a,b)
notequals = lambda a,b: r"%s\not=%s" % (a,b)
augfn = lambda f,x,v: r"[%s\ |\ %s]" % (f, colon(x,v))
apart = lambda G,x: r"%s\ \#\ %s" % (G,x)
ident = lambda i: r"\ {\tt %s}\ " % i
infixident = lambda l,i,r: r"%s%s%s" % (l,ident(i),r)
plus = lambda a,b: "%s + %s" % (a,b)
stepsto = define("stepsto", lambda x,x1: r"%s \rightarrow %s" % (x,x1))
scopeelem = define("scopeelem", lambda v,tau: r"(%s,%s)" % (v,tau))
maybeVal = define("maybeVal", lambda: "\_")
lognot = lambda x: r"\neg(%s)" % x
apply = lambda f, x: r"%s %s" % (f, x)
explicitapply = lambda f, x: apply(f, "(%s)"%x)
stripfn = lambda f, x: r"%s / %s" % (f, x)
hasstack = define("hasstack", lambda P,K: "%s | %s" % (P,K))
hastype = colon
lookup = define("lookup", lambda fn,x,y: """%s(%s) = %s""" % (fn,x,y))
setadd = define('setadd', lambda A,x: "%s \cup \{%s\}" % (A,x))
setrem = define('setrem', lambda A,x: "%s - \{%s\}" % (A,x))
setintersect = define('setintersect', lambda A,B: "%s \\cap %s" % (A,B))
sub = lambda a,i: "%s_{%s}" % (a,i)
forall = lambda x, A, p: "\\forall %s \\in %s. %s" % (x,A,p)
implies = lambda a,b: "%s \\Rightarrow %s" % (a,b)
at = lambda x,y: "%s\ @\ %s" % (x,y)

dom = define('dom', lambda x: aste('dom', x))

def aste(name, *args):
  base = r"{\tt %s}" % name
  if args:
    base += "("
    for i,a in enumerate(args):
      if i > 0:
        base += ","
      base += str(a)
    base += ")"
  return base

# types
x = 'x'
f = 'f'
f_1 = 'f_1'
f_n = 'f_n'
x_1 = 'x_1'
x_2 = 'x_2'
x_i = 'x_i'
x_k = 'x_k'
x_n = 'x_n'
p = 'p'
p1 = "p'"
tau = cmd('tau')
tau1 = cmd("tau'")
tau2 = cmd("tau''")
tau3 = cmd("tau'''")
tau_1 = cmd('tau_1')
tau_2 = cmd('tau_2')
tau_3 = cmd('tau_3')
tau_a = cmd('tau_a')
tau_i = cmd('tau_i')
tau_j = cmd('tau_j')
tau_k = cmd('tau_k')
tau_n = cmd('tau_n')
tau_r = cmd('tau_r')
tau_x = cmd('tau_x')
command = define("commandty", lambda: kw("cmd"))
bool = define("bool", lambda: kw("bool"))
int = define("integer", lambda: kw("int"))
fn = define("function", lambda args,retty: args + rightarrow() + retty)
ptr = define("pointer", lambda tau: "%s *" % tau)
array = define("arraytype", lambda tau: "%s []" % tau)
struct = define("struct", lambda p: aste("struct", p))
tuplety = define("tuple", lambda *args: aste('tuple', *args), varargs=True)
# not really a new type, just convenient
void = define("void", lambda: tuplety())

emptyparams = define("emptyparams", lambda: cdot)
param = define("param", lambda p,f,tau: comma(p,hastype(f,tau)))

def funargs(*args):
  p = emptyparams
  argname = 'a'
  for ty in args:
    p = param(p, argname, ty)
    argname = chr(ord(argname)+1)
  return p

klass(p, newlines=False).member(emptyparams).member(param(p,f,tau))
klass(tau) \
  .member(bool, newline=False) \
  .member(int, newline=False) \
  .member(fn(tau1, tau)) \
  .member(ptr(tau)) \
  .member(array(tau)) \
  .member(struct(p)) \
  .member(command, newline=False) \
  .member(tuplety(tau_1, ldots, tau_n))

# addresses
a = 'a'
a1 = "a'"
l = 'l'
n = 'n'
null = define("anull", lambda: kw("null"))

arrayoffset = define("arrayoffset", lambda a,n: "%s+%s" % (a,n))
fieldoffset = define("fieldoffset", lambda a,f: "%s+%s" % (a,f))

klass(a).member(null).member(l).member(arrayoffset(l,n)).member(fieldoffset(a,f))


# values
v = 'v'
v1 = "v'"
v2 = "v''"
v_1 = 'v_1'
v_f = 'v_f'
v_i = 'v_i'
v_j = 'v_j'
v_k = 'v_k'
v_n = 'v_n'
v_2 = 'v_2'
e = 'e'

builtin("overline")

true = define("true", lambda: kw("true"))
false = define("false", lambda: kw("false"))
integer = define("intliteral", lambda n: overline(n))
address = define("address", lambda a: aste("ptr", a))
arrayval = define("arrayval", lambda a, n: aste('array', a, n))
structval = define("structval", lambda a: aste('rec', a))
funcval = define("func", lambda *args: aste('func', *args), varargs=True)
nop = define("nop", lambda: aste("nop"))

klass(v) \
  .member(true, newline=False) \
  .member(false) \
  .member(integer(n)) \
  .member(address(a)) \
  .member(arrayval(a,n)) \
  .member(structval(a)) \
  .member(funcval(x_1, ldots, x_n, e)) \
  .member(nop)

# expressions
e1 = "e'"
e_1 = 'e_1'
e_2 = 'e_2'
e_3 = 'e_3'
e_a = 'e_a'
e_f = 'e_f'
e_i = 'e_i'
e_j = 'e_j'
e_n = 'e_n'
e_c = 'e_c'
e_t = 'e_t'
e_f = 'e_f'
op = 'op'

binop = define("binop", lambda op,e_1,e_2: aste("binop", op, e_1, e_2))
monop = define("monop", lambda op,e: aste("monop", op, e))
call = define("call", lambda *args: aste("call", *args), varargs=True)
ifexp = define("ifexp", lambda e, et, ef: aste("if", e, et, ef))
decl = define("decl", lambda x,tau,e: aste("decl", x,tau,e))
assign = define("assign", lambda x,e: aste("assign", x, e))
ret = define("return", lambda e: aste("return",e))
loopstm = define("loopstm", lambda e_c, e: aste("loop", e_c, e))
breakstm = define("breakstm", lambda: aste('break'))
continuestm = define("continue", lambda: aste('continue'))
tupleexp = define('tupleexp', lambda *args: aste('', *args), varargs=True)
alloc = define('allocexp', lambda tau: aste('alloc', tau))
allocarray = define('allocarrayexp', lambda tau, e: aste('allocarray', tau, e))

klass(e) \
  .member(x) \
  .member(v) \
  .member(binop(op, e_1, e_2)) \
  .member(monop(op,e)) \
  .member(tupleexp(e_1, ldots, e_n)) \
  .member(call(e_f, e)) \
  .member(ifexp(e_c, e_t, e_f)) \
  .member(decl(x,tau,e)) \
  .member(assign(x,e)) \
  .member(ret(e)) \
  .member(loopstm(e_c, e)) \
  .member(breakstm) \
  .member(continuestm) \
  .member(alloc(tau)) \
  .member(allocarray(tau,e))

# process
P = builtin('mu')
P1 = builtin("mu'")
P2 = builtin("mu''")
pcell = define("pcell", lambda P,a,m: augfn(P,a,m))
plookup = define("plookup", lambda P,a,m: """%s(%s) = %s""" % (P,a,m))

# process typing
S = builtin('Sigma')
S1 = builtin("Sigma'")
slookup = define("slookup", lambda S,a,tau: "%s(%s) = %s" % (S,a,tau))

# operators
binops = [["add", "sub", "mul", "div", "mod"],
          ["bitand", "bitor", "bitxor"],
          ["shl", "shr"],
          ["cmpg", "cmpl", "cmpge", "cmple", "cmpeq", "cmpne"],
          ["seq"],
          ["write", "arrayindex"]]
monops = ["neg", "lognot", "bitnot", "ign", "read"]

opclass = klass(op)

def addOperator(op,newline):
  id = "op"+op
  # hacks: dynamically adding variables to the global scope like this
  cmd = define(id, lambda: aste(op))
  globals()[id] = cmd
  opclass.member(cmd,newline=newline)

def addOperatorGroup(group):
  for op in group:
    addOperator(op, op == group[-1])

map(addOperatorGroup, binops)
addOperatorGroup(monops)

opfield = define("opfield", lambda f=f: aste('field', f))
opclass.member(opfield(f))

# Assignment sets
A = 'A'
A1 = "A'"
A2 = "A''"
A3 = "A'''"
A_1 = 'A_1'
A_2 = 'A_2'
i = 'i'

# Variable contexts
G = builtin("Gamma")
G1 = builtin("Gamma'")
emptyctx = cdot
varctx = define("varctx", lambda G,x,tau: comma(G,hastype(x,tau)))
varlookup = lambda G,x,tau: varctx(G,x,tau)
def nary_varctx(upper, lower=1, var=x, tau=tau):
  return varctx(comma(varctx(emptyctx, sub(var,lower), sub(tau,lower)), ldots), sub(var,upper), sub(tau,upper))

# Loop context
L = "L"
inloop = define("inloop", lambda: ident("inloop"))
notinloop = define("notinloop", lambda: ident("notinloop"))

klass(L, newlines=False).member(inloop).member(notinloop)

# Stacks
hole = cdot

F = "F"
F1 = "F'"
F2 = "F''"
emptyframe = cdot
frameexp = define("frameexp", lambda F,e: comma(F,e))
frameval = define("frameval", lambda F,x,tau,v: comma(F,equals(hastype(x,tau),v)))
framevar = define("framevar", lambda F,x,tau: comma(F,hastype(x,tau)))
frameloop = define("frameloop", lambda F,e_c,e: comma(F,aste('loopctx',e_c,e)))

klass(F, newlines=False) \
  .member(emptyframe) \
  .member(frameexp(F,e)) \
  .member(frameval(F,x,tau,v)) \
  .member(framevar(F,x,tau),newline=True) \
  .member(frameloop(F,e_c,e))

K = "K"
K1 = "K'"
K2 = "K''"
emptystack = define("emptystack", lambda: cdot)
stackframe = define("stackframe", lambda K,F: semi(K,F))

klass(K,newlines=False).member(emptystack).member(stackframe(K,F))

# direction
d = '\\bowtie'
d1 = "\\bowtie'"
pushing = r"\rhd"
returning = r"\lhd"

klass(d, newlines=False).member(pushing).member(returning)

# focus
t = 't'
t1 = "t'"
exn = define("exn", lambda: aste('exn'))

klass(t, newlines=False).member(e).member(exn())

# static semantics
section("Static Semantics", "statics")
define("memcheck", lambda P,S: inferrule(r"%s = %s \\ \forall a \in %s. %s \wedge %s \wedge %s" % (dom(P), dom(S), dom(P), lookup(P,a,v), entails(S, hastype(v,tau)), lookup(S,a,tau)), hastype(P,S)))

define("sigcheck", lambda S,S1: inferrule(r"%s" % forall(a, dom(S), lookup(S,a,explicitapply(S1,a))), r"%s \le %s" % (S,S1)))

# rule declarations
tausmall = ruleset('tausmall', lambda tau=tau: infixident(tau,'small',''))
checkval = ruleset('checkval', lambda S=S,v=v,tau=tau: entails(S,hastype(v,tau)))
checkexp = ruleset('checkexp', lambda S=S,G=G,e=e,tau=tau: entails(semi(S,G), hastype(e,tau)))
canalloc = ruleset('canalloc', lambda tau=tau: infixident(tau,'alloc',''))
checkassign = ruleset('checkassign', lambda G=G,A=A,e=e,A1=A1: entails(G, hastype(e,fn(A,A1))))
checkbinop = ruleset('checkbinop', lambda op=op,tau1=tau1,tau2=tau2,tau=tau: hastype(op, fn("%s \\times %s" % (tau1,tau2), tau)))
checkmonop = ruleset('checkmonop', lambda op=op,tau1=tau1,tau=tau: hastype(op, fn(tau1, tau)))
checkloop = ruleset('checkloop', lambda L=L,e=e: entails(L, "%s %s" % (e, ident('ok'))))
checkonlyreturns = ruleset('onlyreturns', lambda S=S,G=G,e=e,tau=tau: entails(semi(S,G), infixident(e,'canreturn',tau)))
checkdoesreturn = ruleset('doesreturn', lambda e=e: entails(' ', infixident(e,'returns','')))
checkreturns = ruleset('returns', lambda S=S,G=G,e=e,tau=tau: entails(semi(S,G), infixident(e, 'returns', tau)))
checkframetype = ruleset('checkframetype', lambda S=S,A=A,F=F,tau=tau,tau1=tau1: entails(semi(S,A),hastype(F,fn(tau,tau1))))
getframecontext = ruleset('getframecontext', lambda S=S,F=F,G=G: entails(S, equals(aste('ctx',F),G)))
getframeassigned = ruleset('getframeassigned', lambda F=F,A=A: equals(aste('assigned', F), A))
getloopcontext = ruleset('getloopcontext', lambda F=F,L=L: equals(aste('loopnest', F),L))
getinnerloop = ruleset('getinnerloop', lambda F=F,F1=F1: equals(aste('innerloop', F), F1))
dirok = ruleset('dirok', lambda d=d,e=e: "%s\\ %s %s" % (d, e, ident('ok')))
ispending = ruleset('ispending', lambda S=S,G=G,e=e,tau=tau,tau1=tau1,tau2=tau2: entails(semi(S,G), at(infixident(e,"pending",fn(tau,tau1)), tau2)))
checkstack = ruleset('checkstack', lambda S=S,K=K,tau=tau,tau1=tau1: entails(S,hastype(K,fn(tau,tau1))))
checkstate = ruleset('checkstate', lambda S=S,K=K,tau=tau,d=d,t=t: entails(S,hastype(infixident(K,d,t),tau)))
finalstate = ruleset('finalstate', lambda S=S,K=K,t=t: entails(S,infixident(infixident(K,returning,t), 'final', '')))

# rule definitions
def tausmallrule(prefix=''):
  tausmall, = specialize(prefix, globals(), 'tausmall')

  rule('bool', tau=bool)
  rule('int', tau=int)
  rule('ptr', tau=ptr(tau))
  rule('array', tau=array(tau))
  rule('tuple', tau=tupleexp())

  return tausmall

def checkvaluerule(prefix=''):
  tausmall, checkexp, checkassign, checkloop, checkreturns, checkval = specialize(prefix, globals(), 'tausmall', 'checkexp', 'checkassign', 'checkloop', 'checkreturns', 'checkval')

  rule('nop', v=nop, tau=command)
  rule('true', v=true, tau=bool)
  rule('false', v=false, tau=bool)
  rule('int', v=integer(n), tau=int) \
    .premise("n < 2^{31}") \
    .premise("n \ge -2^{31}")
  rule('address', v=address(a), tau=ptr(tau)) \
    .premise(lookup(S,a,tau))
  rule('null', v=address(null), tau=ptr(tau))
  rule('array', v=arrayval(a,n), tau=array(tau)) \
    .premise(forall('i', '[0,n)', lookup(S,arrayoffset(a,'i'),tau)))
  rule('struct', v=structval(a), tau=struct(p)) \
    .premise(forall(hastype('f',tau),p, lookup(S,fieldoffset(a,'f'),tau)))
  rule('func', v=funcval(x_1, ldots, x_n, e), tau=fn(tuplety(tau_1, ldots, tau_n),tau)) \
    .premise(equals(G, nary_varctx(n))) \
    .premise(equals(A, r"\{ x_1, \ldots, x_n \}")) \
    .premise("|A| = n") \
    .premise(checkexp(tau=command)) \
    .premise(checkassign(A1=A)) \
    .premise(checkloop(L=notinloop)) \
    .premise(checkreturns) \
    .premise(tausmall) \
    .premise(tausmall(tau=tau_1)) \
    .premise(ldots) \
    .premise(tausmall(tau=tau_n))

  return checkval

def checkexprule(prefix=''):
  tausmall, checkval, canalloc, checkbinop, checkmonop, checkexp = specialize(prefix, globals(), 'tausmall', 'checkval', 'canalloc', 'checkbinop', 'checkmonop', 'checkexp')

  rule('var', G=varlookup(G,x,tau), e=x)
  rule('value', e=v) \
    .premise(checkval(S,v,tau))
  rule('binop', e=binop(op,e_1,e_2)) \
    .premise(checkbinop()) \
    .premise(checkexp(e=e_1,tau=tau1)) \
    .premise(checkexp(e=e_2,tau=tau2))
  rule('monop', e=monop(op,e)) \
    .premise(checkmonop) \
    .premise(checkexp(tau=tau1))
  rule('tuple', e=tupleexp(e_1, ldots, e_n), tau=tuplety(tau_1, ldots, tau_n)) \
    .premise(checkexp(e=e_1,tau=tau_1)) \
    .premise(ldots) \
    .premise(checkexp(e=e_n,tau=tau_n)) \
    .premise(tausmall(tau=tau_1)) \
    .premise(ldots) \
    .premise(tausmall(tau=tau_n))
  rule('call', e=call(e_f, e)) \
    .premise(checkexp(e=e_f, tau=ptr("(%s)" % fn(tuplety(tau_1, ldots, tau_n),tau)))) \
    .premise(checkexp(tau=tuplety(tau_1, ldots, tau_n)))
  rule('if', e=ifexp(e_c,e_t,e_f)) \
    .premise(checkexp(e=e_c,tau=bool)) \
    .premise(checkexp(e=e_t)) \
    .premise(checkexp(e=e_f))
  rule('decl', e=decl(x,tau,e),tau=command) \
    .premise(checkexp(G=varctx(G,x,tau),tau=command)) \
    .premise(tausmall())
  rule('assign', G=varlookup(G,x,tau), e=assign(x,e), tau=command) \
    .premise(checkexp(G=varctx(G,x,tau))) \
    .premise(tausmall())
  rule('return', e=ret(e),tau=command) \
    .premise(checkexp) \
    .premise(tausmall)
  rule('loop', e=loopstm(e_c,e), tau=command) \
    .premise(checkexp(e=e_c,tau=bool)) \
    .premise(checkexp(tau=command))
  rule('break', e=breakstm, tau=command)
  rule('continue', e=continuestm, tau=command)
  rule('alloc', e=alloc(tau), tau=ptr(tau)) \
    .premise(canalloc())
  rule('allocarray', e=allocarray(tau,e), tau=array(tau)) \
    .premise(checkexp(tau=int)) \
    .premise(canalloc())

  return checkexp

def canallocrule(prefix=''):
  canalloc, = specialize(prefix, globals(), 'canalloc')

  rule('bool', tau=bool)
  rule('int', tau=int)
  rule('ptr', tau=ptr(tau))
  rule('array', tau=array(tau))
  rule('struct', tau=struct(p))

  return canalloc

def checkassignrule(prefix=''):
  checkassign, = specialize(prefix, globals(), 'checkassign')

  declG = varctx(comma(varctx(emptyctx, x_1,tau_1), ldots), x_n, tau_n)
  declA = r"\{x_1, \ldots, x_n\}"

  rule('var', e=x, A1=A) \
    .premise(contains(x,A))
  rule('hole', e=hole, A1=A)
  rule('value', e=v, A1=A)
  rule('binop', e=binop(op,e_1,e_2), A1=A2) \
    .premise(checkassign(e=e_1)) \
    .premise(checkassign(e=e_2,A=A1,A1=A2))
  rule('monop', e=monop(op,e), A1=A) \
    .premise(checkassign(A1=A))
  rule('tuple', e=tupleexp(e_1, ldots, e_n), A1=A) \
    .premise(checkassign(e=e_1,A1=A)) \
    .premise(ldots) \
    .premise(checkassign(e=e_n,A1=A))
  rule('call', e=call(e_f, e), A1=A)
  rule('if', e=ifexp(e_c,e_t,e_f), A1=setintersect(A1,A2)) \
    .premise(checkassign(e=e_c, A1=A)) \
    .premise(checkassign(e=e_t,A=A,A1=A1)) \
    .premise(checkassign(e=e_f,A=A,A1=A2))
  rule('decl', e=decl(x,tau,e), A1=setrem(A1,x)) \
    .premise(doesnotcontain(x, A)) \
    .premise(checkassign(G=varctx(G,x,tau)))
  rule('assign', e=assign(x,e), A1=setadd(A,x)) \
    .premise(checkassign(A1=A))
  rule('return', G=declG, e=ret(e), A1=declA) \
    .premise(checkassign(A1=A))
  rule('loop', e=loopstm(e_c,e), A1=A) \
    .premise(checkassign(e=e_c, A1=A)) \
    .premise(checkassign())
  rule('break', G=declG, e=breakstm, A1=declA)
  rule('continue', G=declG, e=continuestm, A1=declA)
  rule('nop', e=nop, A1=A)
  rule('alloc', e=alloc(tau), A1=A)
  rule('allocarray', e=allocarray(tau,e), A1=A) \
    .premise(checkassign(A1=A))

  return checkassign

def checklooprule(prefix=''):
  checkloop, = specialize(prefix, globals(), 'checkloop')

  rule('var', e=x)
  rule('value', e=v)
  rule('binop', e=binop(op,e_1,e_2)) \
    .premise(checkloop(e=e_1)) \
    .premise(checkloop(e=e_2))
  rule('monop', e=monop(op,e)) \
    .premise(checkloop())
  rule('tuple', e=tupleexp(e_1, ldots, e_n)) \
    .premise(checkloop(e=e_1)) \
    .premise(ldots) \
    .premise(checkloop(e=e_n))
  rule('call', e=call(e_f, e_a)) \
    .premise(checkloop(e=e_f)) \
    .premise(checkloop(e=e_a))
  rule('if', e=ifexp(e_c,e_t,e_f)) \
    .premise(checkloop(e=e_c)) \
    .premise(checkloop(e=e_t)) \
    .premise(checkloop(e=e_f))
  rule('decl', e=decl(x,tau,e)) \
    .premise(checkloop)
  rule('assign', e=assign(x,e)) \
    .premise(checkloop())
  rule('return', e=ret(e)) \
    .premise(checkloop())
  rule('loop', e=loopstm(e_c,e)) \
    .premise(checkloop(e=e_c)) \
    .premise(checkloop(L=inloop))
  rule('break', L=inloop, e=breakstm)
  rule('continue', L=inloop, e=continuestm)
  rule('nop', e=nop)
  rule('alloc', e=alloc(tau))
  rule('allocarray', e=allocarray(tau,e)) \
    .premise(checkloop())

  return checkloop

def checkonlyreturnsrule(prefix=''):
  checkexp, checkonlyreturns = specialize(prefix, globals(), 'checkexp', 'checkonlyreturns')

  rule('binop', e=binop(opseq,e_1,e_2)) \
    .premise(checkonlyreturns(e=e_1)) \
    .premise(checkonlyreturns(e=e_2))
  rule('monop', e=monop(opign, e))
  rule('if', e=ifexp(e_c,e_t,e_f)) \
    .premise(checkonlyreturns(e=e_t)) \
    .premise(checkonlyreturns(e=e_f))
  rule('decl', e=decl(x,tau,e)) \
    .premise(checkonlyreturns(G=varctx(G,x,tau)))
  rule('assign', e=assign(x, e))
  rule('return', e=ret(e)) \
    .premise(checkexp)
  rule('loop', e=loopstm(e_c,e)) \
    .premise(checkonlyreturns)
  rule('break', e=breakstm)
  rule('continue', e=continuestm)
  rule('nop', e=nop)

  return checkonlyreturns

def checkdoesreturnrule(prefix=''):
  checkdoesreturn, = specialize(prefix, globals(), 'checkdoesreturn')

  rule('binoplhs', e=binop(opseq,e_1,e_2)) \
    .premise(checkdoesreturn(e=e_1))
  rule('binoprhs', e=binop(opseq,e_1,e_2)) \
    .premise(checkdoesreturn(e=e_2))
  rule('if', e=ifexp(e_c,e_t,e_f)) \
    .premise(checkdoesreturn(e=e_t)) \
    .premise(checkdoesreturn(e=e_f))
  rule('decl', e=decl(x,tau,e)) \
    .premise(checkdoesreturn)
  rule('return', e=ret(e))

  return checkdoesreturn

def checkreturnsrule(prefix=''):
  tausmall, checkonlyreturns, checkdoesreturn, checkreturns = specialize(prefix, globals(), 'tausmall', 'checkonlyreturns', 'checkdoesreturn', 'checkreturns')

  rule('only') \
    .premise(checkonlyreturns) \
    .premise(checkdoesreturn) \
    .premise(tausmall)

  return checkreturns

def checkbinoprule(prefix=''):
  tausmall, checkbinop = specialize(prefix, globals(), 'tausmall', 'checkbinop')

  def makeBinopRule ((op, tauarg, tauret)):
    if hasattr(tauarg, 'name'):
      argname = tauarg.name
    else:
      # HAX
      argname = tauarg.replace('\\','').replace("{",'').replace("}",'')
    return rule(op.name+argname, op=op, tau1=tauarg, tau2=tauarg, tau=tauret)

  binopRuleData = [
    (opadd, int, int),
    (opsub, int, int),
    (opmul, int, int),
    (opdiv, int, int),
    (opmod, int, int),
    (opbitand, int, int),
    (opbitor, int, int),
    (opbitxor, int, int),
    (opshl, int, int),
    (opshr, int, int),
    (opcmpg, int, bool),
    (opcmpl, int, bool),
    (opcmpge, int, bool),
    (opcmple, int, bool),
    (opcmpeq, int, bool),
    (opcmpne, int, bool),
    (opcmpeq, bool, bool),
    (opcmpne, bool, bool),
    (opcmpeq, ptr(tau), bool),
    (opcmpne, ptr(tau), bool),
  ]

  map(makeBinopRule, binopRuleData)

  rule('seq', op=opseq, tau1=command, tau2=command, tau=command)
  rule('write', op=opwrite, tau1=ptr(tau), tau2=tau, tau=tau) \
    .premise(tausmall(tau))
  rule('arrayindex', op=oparrayindex, tau1=array(tau), tau2=int, tau=ptr(tau))

  return checkbinop

def checkmonoprule(prefix=''):
  tausmall, checkmonop = specialize(prefix, globals(), "tausmall", "checkmonop")
  makeMonopRule = lambda (op, tauarg, tauret): rule(op.name+tauarg.name, op=op, tau1=tauarg, tau=tauret)

  monopRuleData = [
    (opneg, int, int),
    (oplognot, bool, bool),
    (opbitnot, int, int),
  ]
  map(makeMonopRule, monopRuleData)

  rule('ign', op=opign, tau1=tau, tau=command) \
    .premise(tausmall(tau))
  rule('read', op=opread, tau1=ptr(tau), tau=tau) \
    .premise(tausmall(tau))
  rule('field', op=opfield(x_i), tau1=ptr(struct(param(comma(param(emptyparams, f_1, tau_1), ldots), f_n, tau_n))), tau=ptr(tau_i)) \
    .premise("1 \le i \le n")

  return checkmonop

def checkframetyperule(prefix=''):
  checkexp, checkassign, checkloop, onlyreturns, doesreturn, getframecontext, getloopcontext, ispending, getframeassigned, checkframetype = specialize(prefix, globals(), "checkexp", "checkassign", "checkloop", "checkonlyreturns", "checkdoesreturn", "getframecontext", "getloopcontext", "ispending", "getframeassigned", "checkframetype")

  rule('frameexpnoret', F=frameexp(F,e)) \
    .premise(checkframetype(A=A1,tau=tau2)) \
    .premise(checkassign()) \
    .premise(getframecontext()) \
    .premise(getloopcontext()) \
    .premise(checkloop()) \
    .premise(ispending(tau1=tau2, tau2=tau1))
  rule('frameexpret', F=frameexp(F,e)) \
    .premise(doesreturn()) \
    .premise(getframecontext()) \
    .premise(checkassign()) \
    .premise(getloopcontext(L=notinloop)) \
    .premise(checkloop(L=notinloop)) \
    .premise(ispending(tau1=command, tau2=tau1))
  rule('frameval', F=frameval(F,x,tau,v), tau=command) \
    .premise(checkframetype(A=setrem(A,x),tau=command))
  rule('framevar', F=framevar(F,x,"\\tau_{%s}" % x), tau=command) \
    .premise(checkframetype(A=setrem(A,x),tau=command))
  rule('frameloop', F=frameloop(F,e_c,e), tau=command) \
    .premise(getframeassigned(A=A1)) \
    .premise(checkframetype(A=A1, tau=command)) \
    .premise(getframecontext()) \
    .premise(checkexp(e=loopstm(e_c,e), tau=command)) \
    .premise(checkassign(A=A1, A1=A1, e=loopstm(e_c,e))) \
    .premise(getloopcontext()) \
    .premise(checkloop(e=loopstm(e_c, e))) \
    .premise(onlyreturns(e=loopstm(e_c, e), tau=tau1))

  return checkframetype

def getframecontextrule(prefix=''):
  checkval, getframecontext = specialize(prefix, globals(), 'checkval', 'getframecontext')

  rule('empty', F=emptyframe, G=emptyctx)
  rule('exp', F=frameexp(F,e)) \
    .premise(getframecontext)
  rule('var', F=framevar(F,x,tau), G=varctx(G,x,tau)) \
    .premise(getframecontext)
  rule('val', F=frameval(F,x,tau,v), G=varctx(G,x,tau)) \
    .premise(getframecontext) \
    .premise(checkval)
  rule('loop', F=frameloop(F,e_c,e)) \
    .premise(getframecontext)

  return getframecontext

def getframeassignedrule(prefix=''):
  getframeassigned, = specialize(prefix, globals(), 'getframeassigned')

  rule('empty', F=emptyframe, A="\{\}")
  rule('exp', F=frameexp(F,e)) \
    .premise(getframeassigned)
  rule('var', F=framevar(F,x,tau)) \
    .premise(getframeassigned)
  rule('val', F=frameval(F,x,tau,v), A=setadd(A,x)) \
    .premise(getframeassigned) \
    .premise(doesnotcontain(x, A))
  rule('loop', F=frameloop(F,e_c,e)) \
    .premise(getframeassigned)

  return getframeassigned

def getloopcontextrule(prefix=''):
  getloopcontext, = specialize(prefix, globals(), 'getloopcontext')

  rule('empty', F=emptyframe, L=notinloop)
  rule('decl', F=framevar(F,x,tau)) \
    .premise(getloopcontext)
  rule('def', F=frameval(F,x,tau,v)) \
    .premise(getloopcontext)
  rule('exp', F=frameexp(F,e)) \
    .premise(getloopcontext)
  rule('loop', F=frameloop(F, e_c, e), L=inloop)

  return getloopcontext

def getinnerlooprule(prefix=''):
  getinnerloop, = specialize(prefix, globals(), 'getinnerloop')

  rule('decl', F=framevar(F,x,tau)) \
    .premise(getinnerloop)
  rule('def', F=frameval(F,x,tau,v)) \
    .premise(getinnerloop)
  rule('exp', F=frameexp(F,e)) \
    .premise(getinnerloop)
  rule('loop', F=frameloop(F, e_c, e), F1=frameloop(F, e_c, e))

  return getinnerloop

def dirokrule(prefix=''):
  dirok, = specialize(prefix, globals(), 'dirok')

  rule('pushing', d=pushing)
  rule('returning', e=v, d=returning)
  rule('tuple', e=tupleexp(v_1, ldots, v_n), d=returning)

  return dirok

def ispendingrule(prefix=''):
  checkval, checkexp, checkbinop, checkmonop, canalloc, tausmall, onlyreturns, ispending = specialize(prefix, globals(), 'checkval', 'checkexp', 'checkbinop', 'checkmonop', 'canalloc', 'tausmall', 'checkonlyreturns', 'ispending')

  rule('binopl', e=binop(op, cdot, e_2), tau2=tau_r) \
    .premise(checkbinop(tau1=tau, tau=tau1)) \
    .premise(checkexp(e=e_2, tau=tau2)) \
    .premise(implies(equals(tau2,command), onlyreturns(e=e_2, tau=tau_r)))
  rule('binopr', e=binop(op, v1, cdot)) \
    .premise(checkbinop(tau1=tau2, tau=tau1, tau2=tau)) \
    .premise(checkval(v=v1,tau=tau2))
  rule('monop', e=monop(op, cdot)) \
    .premise(checkmonop(tau1=tau,tau=tau1))
  rule('callf', e=call(cdot, e), tau=ptr("(%s)" % fn(tau,tau1))) \
    .premise(checkexp())
  rule('calla', e=call(address(a), cdot)) \
    .premise(checkexp(e=address(a), tau=ptr(fn(tau,tau1))))
  rule('tuple', e=tupleexp(v_1, ldots, "v_{i-1}", cdot, "e_{i+1}", ldots, e_n), tau=tau_i, tau1=tuplety(tau_1, ldots, tau_n)) \
    .premise(checkval(v=v_1,tau=tau_1)) \
    .premise(ldots) \
    .premise(checkval(v="v_{i-1}",tau="\\tau_{i-1}")) \
    .premise(checkexp(e="e_{i+1}",tau="\\tau_{i+1}")) \
    .premise(ldots) \
    .premise(checkexp(e=e_n, tau=tau_n)) \
    .premise(tausmall(tau=tau_1)) \
    .premise(ldots) \
    .premise(tausmall(tau=tau_n))
  rule('if', e=ifexp(cdot, e_t, e_f), tau=bool) \
    .premise(checkexp(e=e_t, tau=tau1)) \
    .premise(checkexp(e=e_f, tau=tau1)) \
    .premise(implies(equals(tau1,command), onlyreturns(e=e_t, tau=tau2))) \
    .premise(implies(equals(tau1,command), onlyreturns(e=e_f, tau=tau2)))
  rule('assign', e=assign(x, cdot), tau1=command) \
    .premise(checkexp(e=x))
  rule('return', e=ret(cdot), tau1=command, tau2=tau) \
    .premise(tausmall)
  rule('allocarray', e=allocarray(tau_a, cdot), tau=int, tau1=array(tau_a)) \
    .premise(canalloc(tau=tau_a))

  return ispending

def checkstackrule(prefix=''):
  checkframetype, getframeassigned, checkstack = specialize(prefix, globals(), 'checkframetype', 'getframeassigned', 'checkstack')

  rule('empty', K=emptystack, tau1=tau)

  rule('nonempty', K=stackframe(K,F)) \
    .premise(checkframetype(tau1=tau2)) \
    .premise(getframeassigned) \
    .premise(checkstack(tau=tau2))

  return checkstack

def checkstaterule(prefix=''):
  checkval, checkexp, checkassign, checkloop, checkstack, onlyreturns, checkreturns, checkframetype, getframeassigned, getframecontext, getloopcontext, getinnerloop, dirok, checkstate = specialize(prefix, globals(), 'checkval', 'checkexp', 'checkassign', 'checkloop', 'checkstack', 'checkonlyreturns', 'checkreturns', 'checkframetype', 'getframeassigned', 'getframecontext', 'getloopcontext', 'getinnerloop', 'dirok', 'checkstate')

  rule('exn', d=returning, t=exn())
  rule('empty', K=emptystack, d=returning, t=e) \
    .premise(checkexp(G=emptyctx)) \
    .premise(dirok(d=returning))
  rule('normal', K=stackframe(K,F), t=e) \
    .premise(getframecontext) \
    .premise(checkexp(tau=tau1)) \
    .premise(getframeassigned) \
    .premise(checkassign) \
    .premise(getloopcontext) \
    .premise(checkloop) \
    .premise(checkframetype(A=A1,tau=tau1,tau1=tau2)) \
    .premise(checkstack(tau=tau2,tau1=tau)) \
    .premise(dirok) \
    .premise(implies(equals(tau1,command), onlyreturns(tau=tau2)))
  rule('returns', K=stackframe(K,F), t=e) \
    .premise(getframecontext) \
    .premise(checkexp(tau=command)) \
    .premise(getframeassigned) \
    .premise(checkassign) \
    .premise(getloopcontext(L=notinloop)) \
    .premise(checkloop(L=notinloop)) \
    .premise(checkreturns(tau=tau2)) \
    .premise(checkstack(tau=tau2,tau1=tau)) \
    .premise(dirok)
  rule('loopbrk', K=stackframe(K,F), d=returning, t=breakstm) \
    .premise(getloopcontext(L=inloop)) \
    .premise(getinnerloop()) \
    .premise(getframeassigned(F=F1)) \
    .premise(checkframetype(F=F1,tau=command,tau1=tau2)) \
    .premise(checkstack(tau=tau2,tau1=tau))
  rule('loopcont', K=stackframe(K,F), d=returning, t=continuestm) \
    .premise(getloopcontext(L=inloop)) \
    .premise(getinnerloop()) \
    .premise(getframeassigned(F=F1)) \
    .premise(checkframetype(F=F1,tau=command,tau1=tau2)) \
    .premise(checkstack(tau=tau2,tau1=tau))
  return checkstate

def finalstaterule(prefix=''):
  checkexp, dirok, finalstate = specialize(prefix, globals(), 'checkexp', 'dirok', 'finalstate')

  rule('exn', K=emptystack, t=exn())
  rule('val', K=emptystack, t=e) \
    .premise(checkexp(G=emptyctx)) \
    .premise(dirok(d=returning))

  return finalstate

defaultrules = [
  tausmallrule(),
  checkvaluerule(),
  checkexprule(),
  canallocrule(),
  checkassignrule(),
  checklooprule(),
  checkonlyreturnsrule(),
  checkdoesreturnrule(),
  checkreturnsrule(),
  checkbinoprule(),
  checkmonoprule(),
  checkframetyperule(),
  getframecontextrule(),
  getframeassignedrule(),
  getloopcontextrule(),
  getinnerlooprule(),
  ispendingrule(),
  dirokrule(),
  checkstackrule(),
  checkstaterule(),
  finalstaterule(),
]

map(lambda x: x.show(), defaultrules)

section("Dynamic Semantics", "dynamics")

state = define('prgstate', lambda P,K,d,t: bar(P,infixident(K,d,t)))
makearrayfn = define('makearray', lambda P=P, a=a, tau=tau, n=n: aste('makearray', P, a, tau, n))

evalbinop = ruleset('evalbinop', lambda P=P,op=op,v_1=v_1,v_2=v_2,P1=P1,t=t: infixident(bar(P, explicitapply(op, comma(v_1,v_2))), r"\rightarrow", bar(P1, t)))
evalmonop = ruleset('evalmonop', lambda P=P, op=op, v=v, t=t: infixident(bar(P, explicitapply(op, v)), r"\rightarrow", t))
smallstep = ruleset('step', lambda P=P,K=K,F=F,d=d,t=t,P1=P1,K1=K1,d1=d1,t1=t1: infixident(state(P,stackframe(K,F),d,t), r"\rightarrow", state(P1,K1,d1,t1)))
allocval = ruleset('allocval', lambda P=P,a=a,tau=tau,P1=P1: equals(aste('allocval', P, a, tau), P1))
makearray = ruleset('makearray', lambda P=P, a=a, tau=tau, n=n, P1=P1: equals(makearrayfn(P,a,tau,n), P1))

def evalbinoprule(prefix=''):
  evalbinop, = specialize(prefix, globals(), 'evalbinop')

  return evalbinop

def evalmonoprule(prefix=''):
  evalmonop, = specialize(prefix, globals(), 'evalmonop')

  return evalmonop

def allocvalrule(prefix=''):
  allocval, = specialize(prefix, globals(), 'allocval')

  rule('bool', tau=bool, P1=pcell(P, a, false))
  rule('int', tau=int, P1=pcell(P, a, integer(0)))
  rule('ptr', tau=ptr(tau), P1=pcell(P, a, address(null)))
  rule('array', tau=array(tau), P1=pcell(P, a, arrayval(null, 0)))
  rule('emptystruct', tau=struct(emptyparams), P1=pcell(P, a, structval(a)))
  rule('struct', tau=struct(param(p, f, tau)), P1=P2) \
    .premise(allocval(tau=struct(p))) \
    .premise(allocval(a=fieldoffset(a,x), P=P1, P1=P2))

  return allocval

def makearrayrule(prefix=''):
  allocval, makearray = specialize(prefix, globals(), 'allocval', 'makearray')

  rule('empty', n=0) \
    .premise(allocval)

  rule('nonempty', n="n+1", P1=P2) \
    .premise(makearray) \
    .premise(allocval(P=P1,P1=P2,a=arrayoffset(a,n)))

  return makearray

def smallsteprule(prefix=''):
  evalbinop, evalmonop, allocval, makearray, step = specialize(prefix, globals(), 'evalbinop', 'evalmonop', 'allocval', 'makearray', 'smallstep')

  rule('val',
      d=pushing, t=v,
      P1=P, K1=stackframe(K, F), d1=returning, t1=v)

  rule('var',
      F=frameexp(frameval(F,x,tau_x,v), ldots), d=pushing, t=x,
      P1=P, K1=stackframe(K,frameexp(frameval(F,x,tau_x,v), ldots)), d1=returning, t1=v)

  rule('pushbinop',
      d=pushing, t=binop(op,e_1,e_2),
      P1=P, K1=stackframe(K,frameexp(F, binop(op,hole,e_2))), d1=pushing, t1=e_1)
  rule('swapbinop',
      F=frameexp(F,binop(op,hole,e_2)), d=returning, t=v,
      P1=P, K1=stackframe(K,frameexp(F,binop(op,v,hole))), d1=pushing, t1=e_2)

  rule('popbinop',
      F=frameexp(F,binop(op, v_1, hole)), d=returning, t=v_2,
      K1=stackframe(K,F), d1=returning, t1=t) \
    .premise(evalbinop)

  rule('pushmonop',
      d=pushing, t=monop(op,e),
      P1=P, K1=stackframe(K, frameexp(F,monop(op, hole))), d1=pushing, t1=e)

  rule('popmonop',
      F=frameexp(F,monop(op,hole)), d=returning, t=v,
      P1=P, K1=stackframe(K, F), d1=returning, t1=t) \
    .premise(evalmonop)

  rule('pushcallfn',
      d=pushing, t=call(e_f, e),
      P1=P, K1=stackframe(K, frameexp(F, call(hole, e))), d1=pushing, t1=e_f)

  rule('pushcallargs',
      F=frameexp(F, call(hole, e)), d=returning, t=v,
      P1=P, K1=stackframe(K, frameexp(F, call(v, hole))), d1=pushing, t1=e)

  rule('finalizecall',
      F=frameexp(F, call(address(a), hole)), d=returning, t=tupleexp(v_1, ldots, v_n),
      P1=P, K1=stackframe(stackframe(K, F), frameval(frameexp(frameval(emptyframe, x_1, tau_1, v_1), ldots), x_n, tau_n, v_n)), d1=pushing, t1=e) \
    .premise(lookup(P,a,funcval(x_1, ldots, x_n, e)))

  rule('callnull',
      F=frameexp(F, call(address(null), hole)), d=returning, t=tupleexp(v_1, ldots, v_n),
      P1=P, K1=stackframe(K,F), d1=returning, t1=exn())

  rule("pushemptytuple",
      d=pushing, t=tupleexp(),
      P1=P, K1=stackframe(K, F), d1=returning, t1=tupleexp())

  rule('pushtupleelem',
      d=pushing, t=tupleexp(e_1, ldots),
      P1=P, K1=stackframe(K, frameexp(F, tupleexp(hole, ldots))), d1=pushing, t1=e_1)

  rule('nexttupleelem',
      F=frameexp(F, tupleexp(ldots, hole, e_i, ldots)), d=returning, t=v,
      P1=P, K1=stackframe(K, frameexp(F, tupleexp(ldots, v, hole, ldots))), d1=pushing, t1=e_i)

  rule('lasttupleelem',
      F=frameexp(F, tupleexp(ldots, hole)), d=returning, t=v,
      P1=P, K1=stackframe(K, F), d1=returning, t1=tupleexp(ldots, v))

  rule('alloc',
      d=pushing, t=alloc(tau_a),
      K1=stackframe(K,F), d1=returning, t1=address(a)) \
    .premise(doesnotcontain(a, dom(P))) \
    .premise(allocval(tau=tau_a))

  rule('pushallocarray',
      d=pushing, t=allocarray(tau_a, e),
      K1=stackframe(K, frameexp(F, allocarray(tau_a, hole))), d1=pushing, t1=e)

  rule('popallocarray',
      F=frameexp(F, allocarray(tau_a, hole)), d=returning, t=integer(n),
      K1=stackframe(K, F), d1=returning, t1=arrayval(a,n)) \
    .premise(doesnotcontain(a, dom(P))) \
    .premise(makearray(tau=tau_a)) \
    .premise(r"n \ge 0")

  rule('popallocarrayerr',
      F=frameexp(F, allocarray(tau, hole)), d=returning, t=integer(n),
      P1=P, K1=stackframe(K, F), d1=returning, t1=exn()) \
    .premise(r"n < 0")

  rule('pushif',
      d=pushing, t=ifexp(e_c,e_t,e_f),
      P1=P, K1=stackframe(K, frameexp(F, ifexp(hole, e_t, e_f))), d1=pushing, t1=e_c)

  rule('popiftrue',
      F=frameexp(F, ifexp(hole, e_t, e_f)), d=returning, t=true,
      P1=P, K1=stackframe(K,F), d1=pushing, t1=e_t)
  rule('popiffalse',
      F=frameexp(F, ifexp(hole, e_t, e_f)), d=returning, t=false,
      P1=P, K1=stackframe(K,F), d1=pushing, t1=e_f)

  rule('pushdecl',
      d=pushing, t=decl(x,tau,e),
      P1=P, K1=stackframe(K, framevar(F,x,tau)), d1=pushing, t1=e)
  rule('popdecl',
      F=framevar(F,x,tau), d=returning, t=nop,
      P1=P, K1=stackframe(K,F), d1=returning, t1=nop)

  rule('pushassign',
      d=pushing, t=assign(x,e),
      P1=P, K1=stackframe(K, frameexp(F,assign(x,hole))), d1=pushing, t1=e)

  rule('popassign',
      F=frameexp(frameexp(frameval(F,x, tau_x, v), ldots), assign(x,hole)), d=returning, t=v1,
      P1=P, K1=stackframe(K,frameexp(frameval(F,x,tau_x,v1), ldots)), d1=returning, t1=nop)

  rule('popassignfirst',
      F=frameexp(frameexp(framevar(F,x,tau_x), ldots), assign(x,hole)), d=returning, t=v1,
      P1=P, K1=stackframe(K,frameexp(frameval(F,x,tau_x,v1), ldots)), d1=returning, t1=nop)

  rule('popassigned',
      F=frameval(F,x,tau_x,v), d=returning, t=nop,
      P1=P, K1=stackframe(K,F), d1=returning, t1=nop)

  rule('pushret',
      d=pushing, t=ret(e),
      P1=P, K1=stackframe(K, frameexp(F, ret(hole))), d1=pushing, t1=e)

  rule('popret',
      F=frameexp(F, ret(hole)), d=returning, t=e,
      P1=P, K1=K, d1=returning, t1=e)

  rule('loop',
      d=pushing, t=loopstm(e_c,e),
      P1=P, K1=stackframe(K, frameloop(F,e_c,e)), d1=pushing, t1=ifexp(e_c, e, breakstm))

  rule('looppop',
      F=frameloop(F,e_c,e), d=returning, t=nop,
      P1=P, K1=stackframe(K,frameloop(F,e_c,e)), d1=returning, t1=continuestm)

  rule('break',
      d=pushing, t=breakstm,
      P1=P, K1=stackframe(K,F), d1=returning, t1=breakstm)

  rule('breakval',
      F=frameval(F,x,tau_x,v), d=returning, t=breakstm,
      P1=P, K1=stackframe(K,F), d1=returning, t1=breakstm)

  rule('breakvar',
      F=framevar(F,x,tau), d=returning, t=breakstm,
      P1=P, K1=stackframe(K,F), d1=returning, t1=breakstm)

  rule('breakloop',
      F=frameloop(F,e_c,e), d=returning, t=breakstm,
      P1=P, K1=stackframe(K,F), d1=returning, t1=nop)

  rule('breakexp',
      F=frameexp(F, e), d=returning, t=breakstm,
      P1=P, K1=stackframe(K,F), d1=returning, t1=breakstm)

  rule('continue',
      d=pushing, t=continuestm,
      P1=P, K1=stackframe(K,F), d1=returning, t1=continuestm)

  rule('continueval',
      F=frameval(F,x,tau_x,v), d=returning, t=continuestm,
      P1=P, K1=stackframe(K,F), d1=returning, t1=continuestm)

  rule('continuevar',
      F=framevar(F,x,tau), d=returning, t=continuestm,
      P1=P, K1=stackframe(K,F), d1=returning, t1=continuestm)

  rule('continueloop',
      F=frameloop(F,e_c,e), d=returning, t=continuestm,
      P1=P, K1=stackframe(K,F), d1=pushing, t1=loopstm(e_c,e))

  rule('continueexp',
      F=frameexp(F, e), d=returning, t=continuestm,
      P1=P, K1=stackframe(K,F), d1=returning, t1=continuestm)

  rule('exnprop',
      d=returning, t=exn(),
      P1=P, K1=emptystack, d1=returning, t1=exn())

  return step

evalbinoprule().show()
evalmonoprule().show()
allocvalrule().show()
makearrayrule().show()
smallsteprule().show()

# Progress defines

getPrefixedRuleset('smallstep', 'KPrime', K=K1, K1=K2)
getPrefixedRuleset('checkstate', 'KPrime', K=K1, K1=K2)
getPrefixedRuleset('checkstack', 'KPrime', K=K1, K1=K2, F=frameexp(F,e), tau=command, tau2=tau1, tau1=tau)
getPrefixedRuleset('checkframetype', 'KPrime', tau2=tau, G=G1, F=F1, tau1=tau2)
getPrefixedRuleset('smallstep', 'progressmodifiedtau', K=K1, K1=K2, tau=tau1)
getPrefixedRuleset('checkexp', 'progressmodifiedtau', tau=tau1)
getPrefixedRuleset('checkexp', 'progressmodifiedtauandgamma', tau=tau1, G=G1)
getPrefixedRuleset('dirok', 'eisv', e=v)
getPrefixedRuleset('checkonlyreturns', 'progresscr', G=varctx(G1,cdot,tau1), tau=tau2)
getPrefixedRuleset('checkexp', 'progressdot', G=varctx(G1,cdot,tau1), tau=tau2)
getPrefixedRuleset('smallstep', 'KPrimeFPrime', K=K1, K1=K2, F=F1, F1=F2, e=e1, v_2=v1, v_1=v)
getPrefixedRuleset('smallstep', 'KPrimeFDPrime', K=K1, K1=K2, F=F2, F1=F2)
getPrefixedRuleset('checkframetype', 'KPrimeFPrime', K=K1, K1=K2, F=F1, tau=tau1, tau1=tau2, tau2=tau3)
getPrefixedRuleset('ispending', 'KPrimeFPrime', K=K1, K1=K2, F=F1, tau=tau1, tau1=tau3, tau2=tau2)
getPrefixedRuleset('checkexp', 'progressassign', G=varctx(G1,cdot,tau1), tau=tau1, e=cdot)
getPrefixedRuleset('dirok', 'progresstuple', e=tupleexp(e_1, ldots, e_n))
getPrefixedRuleset('checkframetype', 'progressbrk', K=K1, K1=K2, F=F1, tau=command, tau1=tau2, tau2=tau3)
getPrefixedRuleset('checkframetype', 'progresstuple', K=K1, K1=K2, F=F1, tau=tuplety(tau_1, ldots, tau_n), tau2=tau3, tau1=tau2, A=A1, A1=A2)
getPrefixedRuleset('ispending', 'progress', v=v_1)
getPrefixedRuleset('ispending', 'lemmacmd', tau=command, tau1=tau)
getPrefixedRuleset('ispending', 'progressbrk', K=K1, K1=K2, F=F1, tau=command, tau1=tau3, tau2=tau3)

emit()

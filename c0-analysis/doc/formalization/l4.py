from proof import *

section("Definitions", "defs")

def callFuncWith(fn, *args, **kwargs):
  old_globals = dict(fn.func_globals)
  fn.func_globals.update(kwargs)
  result = fn(*args)
  fn.func_globals.update(old_globals)
  return result

builtin("rightarrow")
builtin("in")
cdot = builtin("cdot")
ldots = builtin("ldots")
bot = builtin("bot")

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
tau_i = cmd('tau_i')
tau_j = cmd('tau_j')
tau_k = cmd('tau_k')
tau_n = cmd('tau_n')
void = define("void", lambda: kw("void"))
bool = define("bool", lambda: kw("bool"))
int = define("integer", lambda: kw("int"))
fn = define("function", lambda args,retty: args + rightarrow() + retty)
ptr = define("pointer", lambda tau: "%s *" % tau)
array = define("arraytype", lambda tau: "%s []" % tau)
struct = define("struct", lambda x, p: aste("struct", x, p))

emptyparams = define("emptyparams", lambda: cdot)
param = define("param", lambda p,x,tau: comma(p,hastype(x,tau)))

def funargs(*args):
  p = emptyparams
  argname = 'a'
  for ty in args:
    p = param(p, argname, ty)
    argname = chr(ord(argname)+1)
  return p

klass(p, newlines=False).member(emptyparams).member(param(p,x,tau))
klass(tau) \
  .member(void, newline=False) \
  .member(bool, newline=False) \
  .member(int) \
  .member(fn(p, tau)) \
  .member(ptr(tau)) \
  .member(array(tau)) \
  .member(struct(x,p))

# addresses
a = 'a'
a1 = "a'"
l = 'l'
n = 'n'
f = 'f'
null = define("anull", lambda: kw("null"))

arrayoffset = define("arrayoffset", lambda a,n: "%s+%s" % (a,n))
fieldoffset = define("fieldoffset", lambda a,f: "%s+%s" % (a,f))

klass(a).member(null).member(l).member(arrayoffset(a,n)).member(fieldoffset(a,f))

# values
v = 'v'
v1 = "v'"
v2 = "v''"
v_1 = 'v_1'
v_i = 'v_i'
v_j = 'v_j'
v_k = 'v_k'
v_2 = 'v_2'

builtin("overline")

unit = define("unit", lambda: kw("()"))
true = define("true", lambda: kw("true"))
false = define("false", lambda: kw("false"))
integer = define("intliteral", lambda n: overline(n))
address = define("address", lambda a: aste("address", a))
arrayval = define("arrayval", lambda a, n: aste('array', a, n))
structval = define("structval", lambda a,x: aste('struct', a, x))

klass(v) \
  .member(unit) \
  .member(true, newline=False) \
  .member(false) \
  .member(integer(n)) \
  .member(address(a)) \
  .member(arrayval(a)) \
  .member(structval(a,x))

# expressions
e = 'e'
e1 = "e'"
e_1 = 'e_1'
e_2 = 'e_2'
e_3 = 'e_3'
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

klass(e) \
  .member(x) \
  .member(v) \
  .member(binop(op, e_1, e_2)) \
  .member(monop(op,e)) \
  .member(call(l, e_1, ldots, e_n)) \
  .member(ifexp(e_c, e_t, e_f))

# statements
s = 's'
s_1 = 's_1'
s_2 = 's_2'
sbody = 's_{body}'
spost = 's_{post}'
decl = define("decl", lambda x,tau,s: aste("decl", x,tau,s))
assign = define("assign", lambda x,e: aste("assign", x, e))
ret = define("return", lambda e: aste("return",e))
seq = define("seq", lambda s1,s2: aste("seq",s1,s2))
ifstm = define("ifstm", lambda e, s1, s2: aste("if", e, s1, s2))
loopstm = define("loopstm", lambda e, sb: aste("loop", e, sb))
breakstm = define("breakstm", lambda: aste('break'))
continuestm = define("continute", lambda: aste('continue'))
ignorestm = define("ignore", lambda e: aste('ignore', e))

klass(s) \
  .member(decl(x,tau,s)) \
  .member(assign(x,e)) \
  .member(ret(e)) \
  .member(seq(s_1,s_2)) \
  .member(ifstm(e,s_1,s_2)) \
  .member(loopstm(e, s)) \
  .member(breakstm) \
  .member(continuestm) \
  .member(ignorestm(e))

# variable contexts
G = builtin("Gamma")
G1 = builtin("Gamma'")
emptyctx = r"""\lambda.\bot"""
varctx = define("varctx", lambda G,x,tau: augfn(G,x,tau))
varlookup = lambda G,x,tau: equals(explicitapply(G,x),tau)
#klass(G, newlines=False).member(emptyctx).member(varctx(G,x,tau))

# memory cell contents
m = 'm'
memfn = define("memfn", lambda p,tau,s: aste("func", s))
memval = define("memval", lambda v: aste("value",v))

klass(m, newlines=False).member(memfn(p,tau,s)).member(memval(v))

# process
P = builtin('mu')
P1 = builtin("mu'")
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
          ["write", "arrayindex"]]
monops = ["neg", "lognot", "bitnot", "read"]

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


section("Static semantics", "static")

# small types
tausmall = ruleset('tausmall', lambda tau=tau: "%s %s" % (tau,ident('small')))

rule('void', tau=void)
rule('bool', tau=bool)
rule('int', tau=int)
rule('ptr', tau=ptr(tau))
rule('array', tau=array(tau))

# static value checking
checkvalue = ruleset("checkvalue", lambda S=S,v=v,tau=tau: entails(S,hastype(v,tau)))

rule('unit', v=unit, tau=void)
rule('int', v=integer(n), tau=int)
rule('true', v=true, tau=bool)
rule('false', v=false, tau=bool)
rule('addr', v=address(a), tau=ptr(tau)) \
  .premise(slookup(S,a,tau))
rule('null', v=address(null), tau=ptr(tau))
rule('array', v=arrayval(a,n), tau=array(tau)) \
  .premise(r"\forall i \in [0,n) " + slookup(S,arrayoffset(a,"i"),tau))
rule('struct', v=structval(a,x), tau=ptr(struct(x,p))) \
  .premise(equals(p, param(comma(param(emptyparams, x_1, tau_1), ldots), x_n, tau_n))) \
  .premise(r"\forall i \in [1,n] " + slookup(S,fieldoffset(a,x_i),tau_i))

# static expression checking
A = 'A'
A1 = "A'"
A2 = "A''"
A_1 = 'A_1'
A_2 = 'A_2'
def exp(prefix=''):
  checkexp = ruleset("checkexp", lambda S=S,A=A,G=G,e=e,tau=tau: entails(semi(S,A,G), colon(e,tau)), prefix)

  rule('var', e=x) \
    .premise(contains(x,A)) \
    .premise(varlookup(G, x, tau))
  rule('value', e=v) \
    .premise(checkvalue(S,v,tau))
  rule('monop', e=monop(op,e), tau=tau) \
    .premise(hastype(op, fn(tau1,tau))) \
    .premise(checkexp(e=e,tau=tau1))
  rule('binop', e=binop(op,e_1,e_2),tau=tau) \
    .premise(hastype(op, fn(r"%s \times %s" % (tau_1,tau_2),tau))) \
    .premise(checkexp(S,A,G,e_1,tau_1)) \
    .premise(checkexp(S,A,G,e_2,tau_2))
  rule('call', e=call(a, e_1, ldots, e_n)) \
    .premise(slookup(S, a, fn(p,tau))) \
    .premise(equals(p, param(comma(param(emptyparams, x_1, tau_1), ldots), x_n, tau_n))) \
    .premise(hastype(e_1, tau_1)) \
    .premise(ldots) \
    .premise(hastype(e_n, tau_n))
  rule('if', e=ifexp(e_c,e_t,e_f)) \
    .premise(checkexp(e=e_c,tau=bool)) \
    .premise(checkexp(e=e_t)) \
    .premise(checkexp(e=e_f))

  return checkexp

checkexp = exp()

# binary operators
checkbinop = ruleset('checkbinops', lambda op=op,taul=tau_1,taur=tau_2, tauret=tau: hastype(op, r"""%s \times %s \rightarrow %s""" % (taul, taur, tauret)))

makeBinopRule = lambda (op, tauarg, tauret): rule(op.name+tauarg.name, op=op, taul=tauarg, taur=tauarg, tauret=tauret)

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
]

map(makeBinopRule, binopRuleData)

rule('write', op=opwrite, taul=ptr(tau), taur=tau, tauret=tau) \
  .premise(tausmall(tau))
rule('arrayindex', op=oparrayindex, taul=array(tau), taur=int, tauret=ptr(tau))

# unary operators
checkmonop = ruleset("checkmonops", lambda op=op, tauarg=tau, tauret=tau1: hastype(op, r"""%s \rightarrow %s""" % (tauarg, tauret)))

makeMonopRule = lambda (op, tauarg, tauret): rule(op.name+tauarg.name, op=op, tauarg=tauarg, tauret=tauret)

monopRuleData = [
  (opneg, int, int),
  (oplognot, bool, bool),
  (opbitnot, int, int),
]
map(makeMonopRule, monopRuleData)

rule('read', op=opread, tauarg=ptr(tau), tauret=tau) \
  .premise(tausmall(tau))
rule('field', op=opfield(x_i), tauarg=ptr(struct(x, param(comma(param(emptyparams, x_1, tau_1), ldots), x_n, tau_n))), tauret=ptr(tau_i))

# static statement checking (assignment)
def stmassign(prefix=''):
  checkstmassign = ruleset("stmassign", lambda S=S,A=A,G=G,s=s,A1=A1: entails(semi(S,A,G),colon(s,A1)), prefix)

  rule("ret", s=ret(e), A1=A) \
    .premise(checkexp(S,A,G,e,tau))
  rule("assignlocal", s=assign(x,e), A1=r"A \cup \{x\}") \
    .premise(checkexp(S,A,G,e,tau)) \
    .premise(varlookup(G,x,tau))
  rule("decl", s=decl(x,tau,s), A1=r"A' - \{x\}") \
    .premise(checkstmassign(S,A,varctx(G,x,tau),s,A1)) \
    .premise(doesnotcontain(x, dom(G))) \
    .premise(tausmall(tau))
  rule("seq", s=seq(s_1,s_2), A1=A2) \
    .premise(checkstmassign(S,A,G,s_1,A1)) \
    .premise(checkstmassign(S,A1,G,s_2,A2))
  rule("if", s=ifstm(e,s_1,s_2),A1=r"%s \cap %s" % (A_1,A_2)) \
    .premise(checkexp(S,A,G,e,bool)) \
    .premise(checkstmassign(S,A,G,s_1,A_1)) \
    .premise(checkstmassign(S,A,G,s_2,A_2))
  rule('loop', s=loopstm(e, s), A1=A) \
    .premise(checkexp(S,A,G,e,bool)) \
    .premise(checkstmassign(S,A,G,s,A1))
  rule('ignore', s=ignorestm(e),A1=A) \
    .premise(checkexp(S,A,G,e,tau))
  return checkstmassign

checkstmassign = stmassign()

# static statement checking (mayreturn)
mayreturn = define("mayreturn", lambda s,tau: infixident(s,'mayreturn',tau))

checkmayreturn = ruleset("mayreturn", lambda S=S,A=A,G=G,s=s,tau=tau: entails(semi(S,A,G), mayreturn(s,tau)))

rule('decl', s=decl(x,tau,s), tau=tau1) \
  .premise(checkmayreturn(G=varctx(G,x,tau),tau=tau1))
rule('assign', s=assign(e_1,e_2))
rule('ret', s=ret(e)) \
  .premise(checkexp)
rule('seq', s=seq(s_1,s_2)) \
  .premise(checkmayreturn(s=s_1)) \
  .premise(checkmayreturn(s=s_2))
rule('if', s=ifstm(e,s_1,s_2)) \
  .premise(checkmayreturn(s=s_1)) \
  .premise(checkmayreturn(s=s_2))
rule('loop', s=loopstm(e, s)) \
  .premise(checkmayreturn)
rule('ignore', s=ignorestm(e))

# static statement checking (returns)
returns = define("returns", lambda s,tau: infixident(s, 'returns', tau))

def stmreturns(prefix=''):
  checkreturns = ruleset("returns", lambda S=S,A=A,G=G,s=s,tau=tau: entails(semi(S,A,G), returns(s,tau)), prefix)

  rule('decl', s=decl(x,tau,s),tau=tau1) \
    .premise(checkreturns(G=varctx(G,x,tau),tau=tau1))

  rule('ret', s=ret(e)) \
    .premise(checkexp(S,A,G,e,tau))
  rule('seqone', s=seq(s_1,s_2)) \
    .premise(checkreturns(s=s_1))

  rule('seqtwo', s=seq(s_1,s_2)) \
    .premise(checkstmassign(s=s_1)) \
    .premise(checkreturns(s=s_2,A=A1))
  return checkreturns

checkreturns = stmreturns()

# static cell checking
checkaddr = ruleset("checkaddr", lambda S=S,m=m,tau=tau: entails(S,hastype(m,tau)))

rule('val', m=memval(v)) \
  .premise(checkvalue(S,v,tau))
rule('func', m=memfn(p,tau,s),tau=fn(p,tau)) \

# stack control flow
h = 'h'
sigma = builtin('sigma')
sigma1 = builtin("sigma'")

hassign = define("hassign", lambda x: aste("assign", x))
blhs = define("hblhs", lambda op,e: aste("blhs", op, e))
brhs = define("hbrhs", lambda op,v: aste("brhs", op, v))
hmonop = define("hmonop", lambda op: aste("monop", op))
hcall = define("hcall", lambda *args: aste("call", *args), varargs=True)
hret = define("hret", lambda: aste("ret"))
hdel = define("hdelete", lambda x: aste("delete", x))
hswitch = define("hswitch", lambda s_1,s_2: aste("switch", s_1, s_2))
hchoose = define("hchoose", lambda e_1,e_2: aste("choose", e_1, e_2))
hignore = define("hignore", lambda: aste("ign"))

klass(h) \
  .member(s) \
  .member(hassign(x)) \
  .member(blhs(op,e)) \
  .member(brhs(op,v)) \
  .member(hmonop(op)) \
  .member(hcall(x,p,sigma, "e_{i+1}", ldots, e_n)) \
  .member(hret) \
  .member(hdel(x)) \
  .member(hswitch(s_1,s_2)) \
  .member(hchoose(e_1,e_2)) \
  .member(hignore)

# stack frames
F = 'F'
F1 = "F'"
emptyframe = cdot
framecontrol = define("framecontrol", lambda F,h: comma(F,h))

klass(F, newlines=False).member(emptyframe).member(framecontrol(F,h))

# loops contexts
L = 'L'
emptyloopctx = cdot
loopctxentry = define("loopctx", lambda L, F, s, A: comma(L, "(%s,%s;%s)" % (F,s,A)))

klass(L, newlines=False) \
  .member(emptyloopctx) \
  .member(loopctxentry(L,F,s,A))

# stack
K = 'K'
K1 = "K'"
K2 = "K''"
emptystack = define("emptystack", lambda: cdot)
stackframe = define("stackframe", lambda K,F,sigma,L: semi(K,"%s\ \&\ %s" % (colon(F,sigma), L)))

klass(K, newlines=False).member(emptystack).member(stackframe(K,F,sigma,L))

# top
t = 't'
t1 = "t'"
hole = cdot
exn = define("exn", lambda m: aste("exn", m))

klass(t, newlines=False).member(e).member(s).member(hole).member(exn(m))


section("Dynamic semantics", "dynamic")

# frame yield checking
def frameYield(prefix=''):
  checkframeyield = ruleset('checkframeyield', lambda S=S,A=A,G=G,F=F,tau=tau: entails(semi(S,A,G), infixident(F,'yields',tau)), prefix)

  rule('delete', F=framecontrol(F,hdel(x))) \
    .premise(checkframeyield(A=r"A - \{x\}", G=stripfn(G,x))) \
    .premise(varlookup(G, x, tau))
  rule('stmret', F=framecontrol(F,s)) \
    .premise(checkreturns(S,A,G,s,tau))
  rule('stmnoret', F=framecontrol(F,s)) \
    .premise(checkstmassign(S,A,G,s,A1)) \
    .premise(checkframeyield(A=A1))
  return checkframeyield

checkframeyield = frameYield()

# frame control element checking
def genFramecontrol(prefix=''):
  checkframecontrol = ruleset('checkframecontrol', lambda S=S,A=A,G=G,F=F,tauin=tau,tauout=tau1: entails(semi(S,A,G), hastype(F, fn(tauin,tauout))), prefix)

  rule('assign', F=framecontrol(F,hassign(x))) \
    .premise(checkframeyield(S,r"A \cup \{x\}",G,F,tau1)) \
    .premise(varlookup(G,x,tau))

  rule('blhs', F=framecontrol(F,blhs(op,e)), tauout=tau3) \
    .premise(checkexp(S,A,G,e,tau1)) \
    .premise(checkbinop(op,tau,tau1,tau2)) \
    .premise(checkframecontrol(S,A,G,F,tau2,tau3))
  rule('brhs', F=framecontrol(F,brhs(op,v)), tauin=tau1, tauout=tau3) \
    .premise(checkvalue(S,v,tau)) \
    .premise(checkbinop(op,tau,tau1,tau2)) \
    .premise(checkframecontrol(S,A,G,F,tau2,tau3))
  rule('monop', F=framecontrol(F,hmonop(op)), tauout=tau2) \
    .premise(checkmonop(op,tau,tau1)) \
    .premise(checkframecontrol(S,A,G,F,tau1,tau2))
  rule('call', F=framecontrol(F,hcall(l,p,sigma,"e_{i+1}",ldots,e_n)), tauin=tau_i) \
    .premise(slookup(S,l,fn(p1,tau))) \
    .premise(equals(p1, param(comma(param(emptyparams, x_1, tau_1), ldots), x_n, tau_n))) \
    .premise(equals(p, param(comma(param(emptyparams, x_1, tau_1), ldots), "x_{i-1}", r"\tau_{i-1}"))) \
    .premise(r"1 \le k < i") \
    .premise(equals(apply(sigma, x_k), scopeelem(v_k, tau_k))) \
    .premise(hastype(v_k,tau_k)) \
    .premise("i < j \le n") \
    .premise(checkexp(S,A,G,e_j,tau_j)) \
    .premise(checkframecontrol(S,A,G,F,tau))
  rule('ret', F=framecontrol(F,hret), tauout=tau)
  rule('switchret', F=framecontrol(F, hswitch(s_1,s_2)), tauin=bool, tauout=tau) \
    .premise(checkreturns(S,A,G,s_1,tau)) \
    .premise(checkreturns(S,A,G,s_2,tau))
  rule('switchnoret', F=framecontrol(F, hswitch(s_1,s_2)), tauin=bool, tauout=tau) \
    .premise(checkstmassign(S,A,G,s_1,A_1)) \
    .premise(checkstmassign(S,A,G,s_2,A_2)) \
    .premise(checkframeyield(S, r"%s \cap %s" % (A_1,A_2), G, F, tau))
  rule('choose', F=framecontrol(F, hchoose(e_1,e_2)), tauin=bool, tauout=tau) \
    .premise(checkexp(S,A,G,e_1,tau)) \
    .premise(checkexp(S,A,G,e_2,tau))
  rule('ignore', F=framecontrol(F, hignore)) \
    .premise(checkframeyield(S,A,G,F,tau1))
  return checkframecontrol

checkframecontrol = genFramecontrol()

# scope extraction
scope = ruleset('scope', lambda sigma=sigma,G=G: equals(aste('scope', sigma),G))

rule('empty', G=emptyctx) \
  .premise(equals(dom(sigma), r"\{\}"))

rule('nonempty', G=varctx(G,x,tau)) \
  .premise(scope(sigma=stripfn(sigma,x))) \
  .premise(equals(apply(sigma, x), scopeelem(maybeVal, tau)))

# assigned variables extraction

def genAssigned(prefix=''):
  assigned = ruleset('assigned', lambda sigma=sigma,A=A: equals(aste('assigned', sigma), A), prefix)

  rule('def', A=r"\{x\ |\ %s \}" % (equals(apply(sigma, x), scopeelem(v, tau))))
  return assigned

assigned = genAssigned()

# partial stack checking
def partialstack(prefix=''):
  checkpartialstack = ruleset('checkpartialstack', lambda S=S,K=K,tauin=tau,tauout=tau1: entails(S,hastype(K,fn(tauin,tauout))), prefix)

  rule('empty', K=emptystack, tauout=tau)
  rule('nonempty', K=stackframe(K,F,sigma, L), tauout=tau2) \
    .premise(assigned(sigma,A)) \
    .premise(scope(sigma,G)) \
    .premise(checkframecontrol(S,A,G,F,tau,tau1)) \
    .premise(checkpartialstack(S,K,tau1,tau2))
  return checkpartialstack

checkpartialstack = partialstack()

# top checking
def top(prefix=''):
  checktop = ruleset('checktop', lambda S=S,K=K,F=F,sigma=sigma,t=t,tau=tau: entails(S,infixident(plus(stackframe(K,F,sigma,L),t),'yields',tau)), prefix)

  rule('exp', t=e,tau=tau2) \
    .premise(assigned(sigma,A)) \
    .premise(scope(sigma,G)) \
    .premise(checkexp(S,A,G,e,tau)) \
    .premise(checkframecontrol(S,A,G,F,tau,tau1)) \
    .premise(checkpartialstack(S,K,tau1,tau2))

  rule('stmret', t=s,tau=tau1) \
    .premise(assigned(sigma,A)) \
    .premise(scope(sigma,G)) \
    .premise(checkreturns(S,A,G,s,tau)) \
    .premise(checkpartialstack(S,K,tau,tau1))

  rule('stmnoret', t=s, tau=tau1) \
    .premise(assigned(sigma,A)) \
    .premise(scope(sigma,G)) \
    .premise(checkstmassign(S,A,G,s,A1)) \
    .premise(checkframeyield(S,A1,G,F,tau)) \
    .premise(checkpartialstack(S,K,tau,tau1))

  rule('hole', t=hole, tau=tau1) \
    .premise(assigned(sigma,A)) \
    .premise(scope(sigma,G)) \
    .premise(checkframeyield(S,A,G,F,tau)) \
    .premise(checkpartialstack(S,K,tau,tau1))

  return checktop

checktop = top()

# whole stack checking
def wholestack(prefix=''):
  checkwholestack = ruleset('checkwholestack', lambda S=S,K=K,t=t,tau=tau: entails(S,hastype(plus(K,t),tau)), prefix)

  rule('emptyvalue', K=emptystack, t=v) \
    .premise(checkvalue(S,v,tau))
  rule('exception', t=exn(m))
  rule('initialcall', K=emptystack, t=call(l)) \
    .premise(slookup(S,l,fn(emptyparams,tau)))
  rule('nontrivial', K=stackframe(K,F,sigma,L)) \
    .premise(checktop(S,K,F,sigma,t,tau))
  return checkwholestack

checkwholestack = wholestack()

# binary operator evaluation rules

evalbinop = ruleset('evalbinop', lambda P=P,op=op,v_1=v_1,v_2=v_2,P1=P1,t=t: stepsto(hasstack(P, "%s(%s,%s)" % (op,v_1,v_2)), hasstack(P1,t)))

# TODO: fill this out

# unary operator evaluation rules

evalmonop = ruleset('evalmonop', lambda P=P,op=op,v=v,t=t: entails(P,equals("%s(%s)" % (op,v), t)))

# stack transition rules
def stackTransition(prefix=''):
  stackstep = ruleset('stackstep', lambda P=P,K=K,P1=P,K1=K1,t=t,t1=t1: stepsto(hasstack(P,plus(K,t)), hasstack(P1, plus(K1,t1))), prefix)

  def defFrame(elem=None, sg=sigma):
    frame = F
    if elem:
      frame = framecontrol(F, elem)
    return stackframe(K, frame, sg, L)

  rule('pushstm', K=defFrame(), t=seq(s_1,s_2), K1=defFrame(s_2), t1=s_1)
  rule('popstm', K=defFrame(s), t=hole, K1=defFrame(), t1=s)

  rule('pushdel', K=defFrame(), t=decl(x,tau,s), K1=defFrame(hdel(x), sg=augfn(sigma,x,scopeelem(bot,tau))), t1 = s)
  rule('popdel', K=defFrame(hdel(x)), t=hole, K1=defFrame(sg=stripfn(sigma,x)), t1=hole)

  rule('pushassign', K=defFrame(), t=assign(x,e), K1=defFrame(hassign(x)), t1=e)
  rule('popassign', K=defFrame(hassign(x)), t=v, K1=defFrame(sg=augfn(sigma, x, scopeelem(v,tau))), t1=hole) \
    .premise(checkvalue(P,v,tau))

  rule('stepvar', K=defFrame(), t=x, K1=defFrame(), t1=v) \
    .premise(equals(apply(sigma,x), scopeelem(v,tau)))

  rule('pushret', K=defFrame(), t=ret(e), K1=defFrame(hret), t1=e)
  rule('popret', K=defFrame(hret), t=v, K1=K, t1=v)

  rule('pushswitch', K=defFrame(), t=ifstm(e,s_1,s_2), K1=defFrame(hswitch(s_1,s_2)), t1=e)
  rule('popswitchtrue', K=defFrame(hswitch(s_1,s_2)), t=true, K1=defFrame(), t1=s_1)
  rule('popswitchfalse', K=defFrame(hswitch(s_1,s_2)), t=true, K1=defFrame(), t1=s_2)

  rule('pushignore', K=defFrame(), t=ignorestm(e), K1=defFrame(hignore), t1=e)
  rule('popignore', K=defFrame(hignore), t=v, K1=defFrame(), t1=hole)

  rule('steploop', K=defFrame(), t=loopstm(e,s), K1=defFrame(), t1=ifstm(e,seq(s,loopstm(e,s)),ignorestm(false)))
  #rule('stepbreak', K=defFrame(

  rule('pushblhs', K=defFrame(), t=binop(op,e_1,e_2), K1=defFrame(blhs(op,e_2)), t1=e_1)

  rule('pushbrhs', K=defFrame(blhs(op, e)), t=v, K1=defFrame(brhs(op,v)), t1=e)
  rule('popbrhs', K=defFrame(brhs(op, v1)), t=v, K1=defFrame(), t1=t, P1=P1) \
    .premise(evalbinop(v_1=v1,v_2=v))

  rule('pushmonop', K=defFrame(), t=monop(op,e), K1=defFrame(hmonop(op)), t1=e)
  rule('popmonop', K=defFrame(hmonop(op)), t=v, K1=defFrame(), t1=t) \
    .premise(evalmonop(P,op,v,t))

  rule('pushchoose', K=defFrame(), t=ifexp(e_c,e_t,e_f), K1=defFrame(hchoose(e_t,e_f)), t1=e_c)
  rule('popchoosetrue', K=defFrame(hchoose(e_t,e_f)), t=true, K1=defFrame(), t1=e_t)
  rule('popchoosefalse', K=defFrame(hchoose(e_t,e_f)), t=false, K1=defFrame(), t1=e_f)

  rule('pushemptycall', K=K, t=call(a), K1=defFrame(), t1=s) \
    .premise(plookup(P,a, memfn(emptyparams, tau, s))) \
    .premise(equals(dom(sigma), r"\{\}"))

  rule('pushnonemptycall', K=defFrame(), t=call(a, e_1, ldots, e_n), K1=defFrame(hcall(a, p, sigma1, e_2, ldots, e_n)), t1=e_1) \
    .premise(plookup(P, a, memfn(p, tau, s))) \
    .premise(equals(p, param(comma(param(emptyparams, x_1, tau_1), ldots), x_n, tau_n))) \
    .premise(equals(apply(sigma1, x), bot))

  rule('stepargs', K=defFrame(hcall(a, p, sigma1, e_2, ldots, e_n)), t=v, K1=defFrame(hcall(a, p1, augfn(sigma1, x, scopeelem(v, tau)), e_3, ldots, e_n)), t1=e_2) \
    .premise(equals(p, param(comma(param(emptyparams, x_1, tau_1), ldots), x_n, tau_n))) \
    .premise(equals(p1, param(comma(param(emptyparams, x_2, tau_2), ldots), x_n, tau_n))) \
    .premise(hastype(v, tau))

  rule('popcall', K=defFrame(hcall(a, param(emptyparams, x, tau), sigma1)), t=v, K1=stackframe(defFrame(), emptyframe, augfn(sigma1, x, scopeelem(v,tau)), L), t1=s) \
    .premise(plookup(P, a, memfn(p, tau1, s)))

  rule('exn', K=defFrame(), t=exn(m), K1=emptystack, t1=exn(m))
  return stackstep

stackstep = stackTransition()

# final states
finalstate = ruleset('finalstate', lambda P=P, K=K, t=t: entails(P, plus(K,t)) + ident('final'))

rule('val', K=emptystack, t=v)
rule('exn', K=emptystack, t=exn(m))

# progress-specific rule generation
section('Progress', 'progess')
Koverride = {'K': K1, 'K1': K2}
callFuncWith(stackTransition, "Kprime", **Koverride)
callFuncWith(top, "Kprime", **Koverride)
callFuncWith(wholestack, "Kprime", **Koverride)

Foverride = {'F': F1, 'K' : K1}
callFuncWith(genFramecontrol, "Fprime", **Foverride)
callFuncWith(stackTransition, "Fprime", **Foverride)

section('Preservation', 'preservation')
def prevpushassign():
  prefix = 'prevpushassign'
  wsoverrides = {
    't': assign(x,e)
  }
  wsrs = callFuncWith(wholestack, prefix, **wsoverrides)
  wsrule = wsrs.rule('nontrivial')
  topoverrides = {
    's' : assign(x,e),
    'A1' : r'A \cup \{x\}',
    'tau1' : tau,
    'tau' : tau1
  }
  toprs = callFuncWith(top, prefix, **topoverrides)
  toprule = toprs.rule('stmnoret')

  checkstmrs = callFuncWith(stmassign, prefix, A1=r'A \cup \{x\}', tau=tau2)

  toprule.premises[2] = checkstmrs.rule('assignlocal').rule
  wsrule.premises[0] = toprule.rule

  unwind = wsrule.rule

  postfix = 'prevpushassignwind'
  windrule  = callFuncWith(wholestack, postfix, t=e, F=framecontrol(F,hassign(x))).rule('nontrivial')
  topwindrule = callFuncWith(top, postfix, tau2=tau, tau=tau2, F=framecontrol(F, hassign(x))).rule('exp')
  topwindrule.premises[3] = callFuncWith(genFramecontrol, postfix, tau=tau2).rule('assign').rule
  windrule.premises[0] = topwindrule.rule
  wind = windrule.rule

  define("prevpushassignunwind", lambda: unwind)
  define("prevpushassignwind", lambda: wind)

prevpushassign()

def prevpopassign():
  prefix = 'prevpopassign'

  define('prevpopassigntransition', lambda: callFuncWith(stackTransition, prefix, tau=tau2).rule('popassign').rule)

  unwindrule  = callFuncWith(wholestack, prefix, t=v, F=framecontrol(F,hassign(x))).rule('nontrivial')
  topunwindrule = callFuncWith(top, prefix, e=v, tau2=tau, tau=tau2, F=framecontrol(F, hassign(x))).rule('exp')
  topunwindrule.premises[3] = callFuncWith(genFramecontrol, prefix, tau=tau2).rule('assign').rule
  unwindrule.premises[0] = topunwindrule.rule
  unwind = unwindrule.rule

  define('prevpopassignunwind', lambda: unwind)

  prefix = 'prevpopassignwind'

  sg = augfn(sigma, x, scopeelem(v,tau2))
  windrule = callFuncWith(wholestack, prefix, t=hole, sigma=sg).rule('nontrivial')
  topwindrule = callFuncWith(top, prefix, tau1=tau,tau=tau1, sigma=sg, A=r'A \cup \{x\}').rule('hole')

  windrule.premises[0] = topwindrule.rule
  wind = windrule.rule
  define('prevpopassignwind', lambda: wind)

prevpopassign()

def prevstepvar():
  prefix = 'prevstepvar'

  define('prevstepvartransition', lambda: callFuncWith(stackTransition, prefix, tau=tau2).rule('stepvar').rule)

  unwindrule = callFuncWith(wholestack, prefix, t=x).rule('nontrivial')
  topunwindrule = callFuncWith(top, prefix, e=x, tau=tau2, tau2=tau).rule('exp')

  topunwindrule.premises[2] = callFuncWith(exp, prefix, tau=tau2).rule('var').rule

  unwindrule.premises[0] = topunwindrule.rule
  unwind = unwindrule.rule

  define('prevstepvarunwind', lambda: unwind)

  prefix = 'prevstepvarwind'
  windrule = callFuncWith(wholestack, prefix, t=v).rule('nontrivial')
  topwindrule = callFuncWith(top, prefix, e=v, tau=tau2, tau2=tau).rule('exp')

  topwindrule.premises[2] = callFuncWith(exp, prefix, tau=tau2).rule('value').rule

  windrule.premises[0] = topwindrule.rule
  define('prevstepvarwind', lambda: windrule.rule)

prevstepvar()

def prevpushret():
  prefix = 'prevpushretunwind'

  unwindrule = callFuncWith(wholestack, prefix, t=ret(e)).rule('nontrivial')
  topunwindrule = callFuncWith(top, prefix, s=ret(e), tau=tau1, tau1=tau).rule('stmret')

  topunwindrule.premises[2] = callFuncWith(stmreturns, prefix, tau=tau1).rule('ret').rule

  unwindrule.premises[0] = topunwindrule.rule
  define(prefix, lambda: unwindrule.rule)

  prefix = 'prevpushretwind'

  windrule = callFuncWith(wholestack, prefix, F=framecontrol(F,hret), t=e).rule('nontrivial')
  topwindrule = callFuncWith(top, prefix, F=framecontrol(F,hret), tau=tau1, tau2=tau).rule('exp')

  topwindrule.premises[3] = callFuncWith(genFramecontrol, prefix, tau=tau1).rule('ret').rule

  windrule.premises[0] = topwindrule.rule

  define(prefix, lambda: windrule.rule)

prevpushret()

def prevpopret():
  prefix = 'prevpopretunwind'

  unwindrule = callFuncWith(wholestack, prefix, F=framecontrol(F,hret), t=v).rule('nontrivial')
  topunwindrule = callFuncWith(top, prefix, F=framecontrol(F,hret), e=v, tau=tau1, tau2=tau).rule('exp')

  topunwindrule.premises[2] = callFuncWith(exp, prefix, tau=tau1).rule('value').rule

  topunwindrule.premises[3] = callFuncWith(genFramecontrol, prefix, tau=tau1).rule('ret').rule

  unwindrule.premises[0] = topunwindrule.rule

  define(prefix, lambda: unwindrule.rule)

  define(prefix+'partialstack', lambda: topunwindrule.premises[4])

  prefix = 'prevpopretwind'

  overrides = {
    'K' : K1,
    'F' : F1,
    'sigma' : sigma1,
    'A' : A1,
    'G' : G1
  }

  windrule = callFuncWith(wholestack, prefix, t=v, **overrides).rule('nontrivial')

  topwindrule = callFuncWith(top, prefix, e=v, tau2=tau, tau=tau1, tau1=tau2, **overrides).rule('exp')

  topwindrule.premises[2] = callFuncWith(exp, prefix, tau=tau1, **overrides).rule('value').rule

  windrule.premises[0] = topwindrule.rule

  define(prefix, lambda: windrule.rule)

  callFuncWith(partialstack, prefix, tau=tau1, tau2=tau, tau1=tau2, **overrides)

prevpopret()

def prevpushblhs():
  prefix = 'prevpushblhsunwind'
  unwindrule = callFuncWith(wholestack, prefix, t=binop(op,e_1,e_2)).rule('nontrivial')

  topunwindrule = callFuncWith(top, prefix, e=binop(op,e_1,e_2), tau2=tau,tau=tau2).rule('exp')

  expunwindrule = callFuncWith(exp, prefix, tau=tau2).rule('binop')

  topunwindrule.premises[2] = expunwindrule.rule

  unwindrule.premises[0] = topunwindrule.rule

  define(prefix, lambda: unwindrule.rule)

  prefix = 'prevpushblhswind'

  windrule = callFuncWith(wholestack, prefix, t=e_1, F=framecontrol(F, blhs(op, e_2))).rule('nontrivial')
  topwindrule = callFuncWith(top, prefix, e=e_1, F=framecontrol(F, blhs(op,e_2)), tau2=tau, tau=tau_1).rule('exp')

  fywindrule = callFuncWith(genFramecontrol, prefix, e=e_2, tau=tau_1, tau3=tau1, tau1=tau_2).rule('blhs')

  topwindrule.premises[3] = fywindrule.rule

  windrule.premises[0] = topwindrule.rule

  define(prefix, lambda: windrule.rule)

prevpushblhs()

def prevpushbrhs():
  prefix = 'prevpushbrhsunwind'

  unwindrule = callFuncWith(wholestack, prefix, F=framecontrol(F, blhs(op,e)), t=v).rule('nontrivial')
  topunwindrule = callFuncWith(top, prefix, e=v, F=framecontrol(F, blhs(op,e)), tau2=tau, tau=tau_1).rule('exp')

  fyunwindrule = callFuncWith(genFramecontrol, prefix, tau=tau_1, tau3=tau1, tau1=tau_2).rule('blhs')

  topunwindrule.premises[3] = fyunwindrule.rule

  unwindrule.premises[0] = topunwindrule.rule

  define(prefix, lambda: unwindrule.rule)

  prefix = 'prevpushbrhswind'

  windrule = callFuncWith(wholestack, prefix, t=e, F=framecontrol(F,brhs(op,v))).rule('nontrivial')
  topwindrule = callFuncWith(top, prefix, tau2=tau, tau=tau_2, F=framecontrol(F, brhs(op,v))).rule('exp')

  fywindrule = callFuncWith(genFramecontrol, prefix, tau3=tau1, tau1=tau_2, tau=tau_1).rule('brhs')

  topwindrule.premises[3] = fywindrule.rule

  windrule.premises[0] = topwindrule.rule

  define(prefix, lambda: windrule.rule)

prevpushbrhs()

def prevpopbrhs():
  prefix = 'prevpopbrhsunwind'

  unwindrule = callFuncWith(wholestack, prefix, t=v, F=framecontrol(F,brhs(op,v1))).rule('nontrivial')
  topunwindrule = callFuncWith(top, prefix, e=v, tau2=tau, tau=tau_2, F=framecontrol(F,brhs(op,v1))).rule('exp')
  fyunwindrule = callFuncWith(genFramecontrol, prefix, v=v1, tau3=tau1, tau1=tau_2, tau=tau_1).rule('brhs')

  topunwindrule.premises[3] = fyunwindrule.rule
  unwindrule.premises[0] = topunwindrule.rule

  define(prefix, lambda: unwindrule.rule)

  prefix = 'prevpopbrhswind'

  windrule = callFuncWith(wholestack, prefix, t=v2).rule('nontrivial')

  topwindrule = callFuncWith(top, prefix, e=v2, tau=tau2, tau2=tau).rule('exp')

  windrule.premises[0] = topwindrule.rule

  define(prefix, lambda: windrule.rule)

prevpopbrhs()

def prevpushmonop():
  prefix = 'prevpushmonopunwind'

  unwindrule = callFuncWith(wholestack, prefix, t=monop(op,e)).rule('nontrivial')
  topunwindrule = callFuncWith(top, prefix, e=monop(op,e), tau2=tau, tau=tau2).rule('exp')


  topunwindrule.premises[2] = callFuncWith(exp, prefix, tau=tau2, tau1=tau3).rule('monop').rule

  unwindrule.premises[0] = topunwindrule.rule

  define(prefix, lambda: unwindrule.rule)

  prefix = 'prevpushmonopwind'

  windrule = callFuncWith(wholestack, prefix, t=e, F=framecontrol(F,hmonop(op))).rule('nontrivial')
  topwindrule = callFuncWith(top, prefix, tau=tau3, tau2=tau, F=framecontrol(F,hmonop(op))).rule('exp')

  fcwindrule = callFuncWith(genFramecontrol, prefix, tau=tau3, tau2=tau1, tau1=tau2).rule('monop')

  topwindrule.premises[3] = fcwindrule.rule
  windrule.premises[0] = topwindrule.rule

  define(prefix, lambda: windrule.rule)

prevpushmonop()

def prevpopmonop():
  prefix = 'prevpopmonopunwind'

  unwindrule = callFuncWith(wholestack, prefix, t=v, F=framecontrol(F,hmonop(op))).rule('nontrivial')
  topunwindrule = callFuncWith(top, prefix, e=v, tau=tau3, tau2=tau, F=framecontrol(F,hmonop(op))).rule('exp')

  fcunwindrule = callFuncWith(genFramecontrol, prefix, tau=tau3, tau2=tau1, tau1=tau2).rule('monop')

  topunwindrule.premises[3] = fcunwindrule.rule
  unwindrule.premises[0] = topunwindrule.rule

  define(prefix, lambda: unwindrule.rule)

  prefix = 'prevpopmonopwind'

  windrule = callFuncWith(wholestack, prefix, t=v1).rule('nontrivial')
  topwindrule = callFuncWith(top, prefix, e=v1, tau2=tau, tau=tau2).rule('exp')

  #topwindrule.premises[3] = fcwindrule.rule
  windrule.premises[0] = topwindrule.rule

  define(prefix, lambda: windrule.rule)

prevpopmonop()

emit()

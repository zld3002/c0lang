# the following are SML-NJ specific defines
SML = sml
MLLEX = ml-ulex
MLYACC = ml-yacc

# buildid target "redundant" if called from ../Makefile, but who cares?
cc0 parse3: buildid FORCE
	echo 'use "compile-cc0-parse3.sml";' | ${SML}
parse2: buildid lexfiles FORCE
	echo 'use "compile-cc0-parse2.sml";' | ${SML}

parse1: buildid parsefiles FORCE
	echo 'use "compile-cc0-parse1.sml";' | ${SML}

csharp: buildid parsefiles FORCE
	echo 'use "compile-cc0-csharp.sml";' | ${SML}

parse1/c0.lex.sml: parse1/c0.lex
	${MLLEX} --ml-lex-mode parse1/c0.lex

parse1/c0.grm.sml: parse1/c0.grm
	${MLYACC} parse1/c0.grm

lexfiles: parse1/c0.lex.sml

parsefiles: parse1/c0.lex.sml parse1/c0.grm.sml

# always build buildid.sml
.PHONY: buildid
buildid:
	rm -f top/buildid.sml
	bin/buildid >top/buildid.sml

clean:
	find . -type d -name .cm | xargs rm -rf
	${RM} parse/*.lex.* parse/*.grm.*
	find . -type f | grep '~$$' | xargs ${RM}
	${RM} bin/cc0.heap.*
	${RM} sample/*.c sample/*.h

TAGS: clean
	${RM} TAGS
	bin/create-tags *.cm *.sml */*.lex */*.grm */*.sml

FORCE: 

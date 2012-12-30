# the following are SML-NJ specific defines
SML = sml
MLLEX = ml-ulex
MLYACC = ml-yacc

# buildid target "redundant" if called from ../Makefile, but who cares?
cc0: buildid FORCE
	echo 'use "compile-cc0.sml";' | ${SML}

csharp: buildid parsefiles FORCE
	echo 'use "compile-cc0-csharp.sml";' | ${SML}

# always build buildid.sml
.PHONY: buildid
buildid:
	rm -f ../buildid.sml
	bin/buildid > ../buildid.sml

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

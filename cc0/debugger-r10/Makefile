SML = sml

compile:
	echo 'CM.make "debugger.cm";' | ${SML}

clean:
	find . -type d -name .cm | xargs rm -rf
	rm parser/c0.grm.*
	rm parser/c0.lex.*


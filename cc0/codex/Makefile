SML = sml

.PHONY: code
code:
	echo 'use "smlnj-go.sml";' | ${SML}

clean:
	find . -type d -name .cm | xargs rm -rf
	find . -type f | grep '~$$' | xargs ${RM}
	${RM} codex.heap.*

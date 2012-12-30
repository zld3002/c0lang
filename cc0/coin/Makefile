SML = sml

.PHONY: coin coin-exec clean
coin:
	echo 'use "smlnj-go.sml";' | ${SML}

coin-exec: 
	echo 'use "coin-exec-smlnj.sml";' | ${SML}

clean:
	find ../cymbol -type d -name .cm | xargs rm -rf
	find . -type d -name .cm | xargs rm -rf
	find . -type f | grep '~$$' | xargs ${RM}
	${RM} coin*.heap.*

INSTALL_TARGET:=c0.typesafety.net:/home/www/c0/doc/


### $(call CLEAN,file,exts) removes file.xyz with xyz in exts
define CLEAN
for ext in $2; do  \
  rm -f $1.$$ext;  \
done
endef

DEL:=aux log out pdf toc idx ilg ind

.PHONY: help c0-libraries c0-reference cc0-guide install clean

help:
	@echo "make [help]        -- print these instructions"
	@echo "make c0-libraries  -- compile the C0 library documentation"
	@echo "make c0-reference  -- compile the C0 language reference"
	@echo "make cc0-guide     -- compile the cc0 users guide"
	@echo "make install       -- compile and install all C0 documentation"
	@echo "make clean         -- remove temporary files"
	@echo ""


c0-libraries:
	pdflatex c0-libraries.tex
	@makeindex c0-libraries
	@pdflatex c0-libraries.tex
	@pdflatex c0-libraries.tex

c0-reference:
	pdflatex c0-reference.tex

cc0-guide:
	pdflatex cc0-users-guide.tex

install: c0-libraries c0-reference cc0-guide
	scp c0-libraries.pdf c0-reference.pdf cc0-users-guide.pdf \
	    $(INSTALL_TARGET)
	@make clean

clean:
	@$(call CLEAN,c0-libraries,$(DEL))
	@$(call CLEAN,c0-reference,$(DEL))
	@$(call CLEAN,cc0-users-guide,$(DEL))

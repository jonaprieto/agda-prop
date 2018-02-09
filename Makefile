.PHONY : default
default : clean test

.ONESHELL:
.PHONY : checklines
checklines :
	@grep '.\{80,\}' -l --recursive src; \
		status=$$?; \
		if [ $$status = 0 ]; \
		then echo "Lines found with more than 80 characters!"; \
		else echo "Succeed!"; \
		fi


.PHONY : clean
clean :
	- find . -name "*.agdai" -type f -delete

.PHONY : test
test :
	agda src/Data/PropFormula.agda --verbose=0
	agda test/ex-andreas-abel.agda --verbose=0
	agda test/nform.agda --verbose=0

.PHONY: listings
listings: 
	agda -i. -isrc --html --html-dir=docs README.agda -v0
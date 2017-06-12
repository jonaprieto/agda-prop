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
	agda src/Data/Prop.agda --verbose=0
	agda test/ex-andreas-abel.agda --verbose=0

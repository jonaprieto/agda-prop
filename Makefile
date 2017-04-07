.PHONY : test
test :
	cd src/Data/ && agda Prop.agda

.PHONY : clean
clean :
	- find . -name "*.agdai" -type f -delete


default : build

build :
	./build.sh

cloc :
	cloc --read-lang-def=cloc-lang-def --by-file *.thy


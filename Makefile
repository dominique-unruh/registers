
default : build

build :
	./build.sh

document/outline.pdf : build

cloc :
	cloc --read-lang-def=cloc-lang-def --by-file *.thy

registers.zip : $(wildcard *.thy) ROOT ROOTS $(wildcard bounded-operators/*.thy) bounded-operators/ROOT README.md .fake-session-dir/1/.gitignore bounded-operators/document/root.tex bounded-operators/fake-session-dir/1/empty
	zip $@ $^

WWW = /home/unruh/svn/home/www-ut/
upload : registers.zip document/outline.pdf
	cp registers.zip $(WWW)
	cp document/outline.pdf $(WWW)/registers-isabelle-theories-outline.pdf
	cd $(WWW) && ./up


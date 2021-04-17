
default : build

build :
	./build.sh

document/outline.pdf : build

cloc :
	cloc --read-lang-def=cloc-lang-def --by-file *.thy

lvalues-isabelle-theories.zip : $(wildcard *.thy) ROOT ROOTS $(wildcard bounded-operators/*.thy) bounded-operators/ROOT README.md .fake-session-dir/1/.gitignore bounded-operators/document/root.tex bounded-operators/fake-session-dir/1/empty
	zip $@ $^

WWW = /home/unruh/svn/home/www-ut/
upload : lvalues-isabelle-theories.zip document/outline.pdf
	cp lvalues-isabelle-theories.zip $(WWW)
	cp document/outline.pdf $(WWW)/lvalues-isabelle-theories-outline.pdf
	cd $(WWW) && ./up


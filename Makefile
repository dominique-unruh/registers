
default : build

build :
	./build.sh

document/outline.pdf : build

cloc :
	cloc --read-lang-def=cloc-lang-def --by-file *.thy

Laws_Classical.thy Laws_Quantum.thy :
	python3 instantiate_laws.py

registers.zip : $(wildcard *.thy) Laws_Classical.thy Laws_Quantum.thy ROOT ROOTS $(wildcard bounded-operators/*.thy) $(wildcard bounded-operators/extra/*.thy) bounded-operators/ROOT README.md .fake-session-dir/1/.gitignore bounded-operators/document/root.tex bounded-operators/fake-session-dir/1/empty instantiate_laws.py document/root.tex
	zip $@ $^

test : registers.zip document/outline.pdf
	rm -v /opt/Isabelle2021/heaps/*/Bounded_Operators*
	rm -v /opt/Isabelle2021/heaps/*/Registers*
	rm -rf /tmp/registers-test
	mkdir /tmp/registers-test
	unzip -d /tmp/registers-test registers.zip
	cd  /tmp/registers-test && /opt/Isabelle2021/bin/isabelle build -v -D .

WWW = /home/unruh/svn/home/www-ut/
upload : registers.zip document/outline.pdf
	cp registers.zip $(WWW)
	cp document/outline.pdf $(WWW)/registers-isabelle-theories-outline.pdf
	cd $(WWW) && ./up


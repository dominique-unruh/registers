ISABELLE_DIR=/opt/Isabelle2021
ISABELLE=$(ISABELLE_DIR)/bin/isabelle
NAME=Registers
THYS=Laws_Complement Classical_Extra Teleport Laws_Complement_Quantum Pure_States Axioms \
	Axioms_Classical Axioms_Quantum Laws Axioms_Complement Axioms_Complement_Quantum \
	Laws_Classical Classical_Extra Finite_Tensor_Product_Matrices Finite_Tensor_Product Misc \
	Laws_Quantum QHoare Quantum_Extra2 Quantum_Extra Quantum Teleport

default : build

build :
	./build.sh

document/outline.pdf : build

cloc :
	cloc --read-lang-def=cloc-lang-def --by-file *.thy

Laws_Classical.thy Laws_Quantum.thy :
	python3 instantiate_laws.py

registers.zip : $(filter-out Experiments.thy, $(wildcard *.thy)) Laws_Classical.thy Laws_Quantum.thy ROOT ROOTS $(wildcard bounded-operators/*.thy) $(wildcard bounded-operators/extra/*.thy) bounded-operators/ROOT README.md .fake-session-dir/1/.gitignore bounded-operators/document/root.tex bounded-operators/fake-session-dir/1/empty instantiate_laws.py document/root.tex
	( git describe --tags --long --always --dirty --broken && git describe --always --all ) > GITREVISION
	zip $@ $^ GITREVISION

test :
	output=$$(git status --porcelain) && [ -z "$$output" ]
	git submodule foreach git clean -fdx
	make registers.zip
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

registers-afp.zip : ROOT.AFP document/root.tex document/root.bib LICENSE $(THYS:%=%.thy) instantiate_laws.py
	rm -rf tmp $@
	mkdir -p tmp/$(NAME)
	cp --parents $^ tmp/$(NAME)
	mv tmp/$(NAME)/ROOT.AFP tmp/$(NAME)/ROOT
	cd tmp && zip -r $@ $(NAME)
	mv tmp/$@ .

test-afp : registers-afp.zip
	rm -rf tmp
	mkdir -p tmp
	cd tmp && unzip ../$^
	cd tmp/$(NAME) && "$(ISABELLE)" build -b -d . -v $(NAME)

set -e

./instantiate_laws.py

/opt/Isabelle2021/bin/isabelle build -v -d . -b Registers

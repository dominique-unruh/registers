#!/bin/bash

set -e

DIR="$(dirname "$BASH_SOURCE[0]")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/Quantum.thy")
else
    FILES=()
fi

ISABELLE_DIR=/opt/Isabelle2021

"$ISABELLE_DIR/bin/isabelle" jedit -l Bounded_Operators -d . "$ISABELLE_DIR/src/Pure/ROOT.ML" "${FILES[@]}" "$@" &

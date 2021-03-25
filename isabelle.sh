#!/bin/bash

set -e

DIR="$(dirname "$BASH_SOURCE[0]")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/Quantum2.thy")
else
    FILES=()
fi

SESSION=Bounded_Operators-Prerequisites

ISABELLE_DIR=/opt/Isabelle2021

"$ISABELLE_DIR/bin/isabelle" jedit -l "$SESSION" -d . "$ISABELLE_DIR/src/Pure/ROOT.ML" "${FILES[@]}" "$@" &

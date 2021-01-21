#!/bin/bash

set -e

DIR="$(dirname "$BASH_SOURCE[0]")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/All.thy")
else
    FILES=()
fi

/opt/Isabelle2021-RC2/bin/isabelle jedit -l HOL "${FILES[@]}" "$@"

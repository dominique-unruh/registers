#!/bin/bash

set -e

DIR="$(dirname "$BASH_SOURCE[0]")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/All.thy")
else
    FILES=()
fi

/opt/Isabelle2020/bin/isabelle jedit -l HOL "${FILES[@]}" "$@"

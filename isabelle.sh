#!/bin/bash

set -e

DIR="$(dirname "$BASH_SOURCE[0]")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/Laws.thy")
else
    FILES=()
fi

/opt/Isabelle2021/bin/isabelle jedit -l Lots-Of-Stuff "${FILES[@]}" "$@"

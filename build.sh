#!/bin/bash

set -e

TMP_DIR=$(mktemp -d -t isabelle-build-XXXXXXXXXXXXXX)

/opt/Isabelle2021/bin/isabelle document -O $TMP_DIR -d . "$@" LValues
cp -v $TMP_DIR/document.pdf lvalues-isabelle.pdf
evince lvalues-isabelle.pdf &

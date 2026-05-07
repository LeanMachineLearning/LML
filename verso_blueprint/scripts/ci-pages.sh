#!/usr/bin/env bash


lake build
lake exe blueprint-gen --output _out/site
mkdir -p _out/site/html-multi/static
cp static_files/* _out/site/html-multi/static

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-preview-manifest.json

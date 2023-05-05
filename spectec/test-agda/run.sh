#!/usr/bin/env bash

# Copy the spec and patch it to minispec
cp -r ../spec minispec
cd minispec && patch -s -p0 -i minispec.patch  --read-only=ignore && cd ..

# Compile the spec to Agda
../src/exe-watsup/main.exe --agda --sub --totalize minispec/*.watsup -o "$1"

# Run Agda
# The `sed` incantation is needed to remove (user-specific) absolute paths in Agda output.
agda "$1" | sed -e "s/\/.*\/_build\///g"

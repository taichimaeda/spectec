# Preview

```sh
$ dune exec ../src/exe-watsup/main.exe -- --agda ../minispec/*.watsup -o output.agda
$ cat output.agda
$ agda output.agda | sed -e "s/(.*\/_build\//(/g"
Checking output (default/test-agda/output.agda).
```

The `sed` incantation is needed to replace

    Checking output (/ABSOLUTE/PATH/TO/USER/FOLDER/spectec/_build/default/test-agda/output.agda).

with

    Checking output (default/test-agda/output.agda).

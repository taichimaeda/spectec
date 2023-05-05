# Agda backend for Wasm SpecTec

A backend translating a Wasm specification into Agda.

## Module structure

- `Gen` - functions exposing the backend outside
- `Ir` - internal representation of the part of Agda we are using
- `Il2ir` - translating from the internal language `Il` into the `Ir`
- `Print` - writing out `Ir` representation into actual `.agda` files

## General plan

- [x] trim down Wasm to miniWasm, a minimal core (eg. without memory, exports, …)
- [ ] ensure the backend produces valid Agda code without holes
- [ ] once that is done, prove safety
- [ ] repeat the process for your favourite extension (full Wasm, MiniWasmFx, …)

## Observations

- Agda is fine with multiple `data` constructors sharing the same name. Similarly, it is fine with multiple `record` fields sharing the same name. However, no `data` constructor may have the same name as any `record` field.
- Agda needs `record` projections to be annotated with the type name, eg. `RECNAME.fieldname`. Only the latter is available in `Il`.

## TODOs

A list of minor issues that need to be resolved at some point. (We are working on a branch and we do not want to pollute the main GitHub repo with them.)

- sort out whether comparison is a boolean or an operation
- mixfix operators
- use a pretty-printer for Agda output
- use size proofs when indexing

## Workflow

    ocamlformat --enable-outside-detected-project -i src/backend-agda/*.{ml,mli}
    && make
    && patch -i minispec.patch -d spec
    && ./watsup --agda --sub --totalize spec/*.watsup -o test-agda/minispec.agda
    && patch -R -i minispec.patch -d spec
    && (cd test-agda && agda minispec.agda)

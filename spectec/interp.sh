set -e
make

./watsup spec/wasm-2.0/*.watsup --test-version 2 --interpreter "test-interpreter/spec-test-2"

#!/bin/sh
# Python 拡張モジュール tlvm を cargo で build し、このディレクトリに tlvm.abi3.so として置く。
# 使い方：crates/tlvm-py/build.sh（CARGO_TARGET_DIR を設定していればそこへ build する）
set -eu
here=$(cd "$(dirname "$0")" && pwd)
target=${CARGO_TARGET_DIR:-$here/target}
cargo build --release --locked --manifest-path "$here/Cargo.toml" --target-dir "$target"
case "$(uname -s)" in
  Darwin) lib=libtlvm.dylib ;;
  *) lib=libtlvm.so ;;
esac
cp "$target/release/$lib" "$here/tlvm.abi3.so"
echo "$here/tlvm.abi3.so"

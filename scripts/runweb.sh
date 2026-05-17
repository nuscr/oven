#!/bin/bash

set -euo pipefail

BASE_DIR=$(dirname "$(realpath "$0")")/..
OUT_DIR=$BASE_DIR/_site
WEB_DIR=$BASE_DIR/web

if ! command -v python3 &> /dev/null; then
  echo "error: 'python3' is not installed."
  exit 1
fi

echo "Building and deploying to $OUT_DIR..."
WHERE="$OUT_DIR" make -C "$WEB_DIR" deploy

echo "Serving at http://localhost:3000"
python3 -m http.server 3000 --directory "$OUT_DIR"

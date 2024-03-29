#! /bin/bash
set -euo pipefail
# Generate the examples.ml file
WEB_DIR="$(realpath "$(dirname "$0")")"
BRAID_DIR="$(realpath "$WEB_DIR/..")"
(echo 'let list = [';
(while read -r file; do
    echo -n "\"$file\","
    echo -n '"'
    sed 's/"/\\"/g' < "$BRAID_DIR/$file"
    echo '";';
done) < "$WEB_DIR/examplelist.txt"
echo ']') > examples.ml

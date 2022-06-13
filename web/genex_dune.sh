#! /bin/bash
set -euo pipefail
# Generate the examples.ml file
WEB_DIR="$(realpath "$(dirname "$0")")"
NU2SCR_DIR="$(realpath "$WEB_DIR/..")"
(echo 'let list = [';
(while read -r file; do
    echo -n "\"$file\","
    echo -n '"'
    sed 's/"/\\"/g' < "$NU2SCR_DIR/$file"
    echo '";';
done) < "$WEB_DIR/examplelist.txt"
echo ']') > examples.ml

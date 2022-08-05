#!/usr/bin/env bash

find examples -name '*.synmpst' -print | xargs ./_build/default/bin/main.exe

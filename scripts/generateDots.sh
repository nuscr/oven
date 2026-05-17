#!/usr/bin/env bash

find examples -name '*.oven' -print | xargs ./_build/default/bin/main.exe

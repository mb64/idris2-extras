#!/bin/bash

_fail=0

fail() {
    echo "TEST FAILED: $1"
    _fail=1
}

IDRIS_ARGS="--find-ipkg -q --no-banner -o test"

for file in $(find tests -name '*.idr' -type f | sort) ; do
    echo "Testing $file ..."
    if echo "$file" | grep -q fail ; then
        # Test should not compile
        idris2 $IDRIS_ARGS "$file" &>/dev/null && fail "$file" \
            || echo "$file: expected failure"
    else
        # Test should compile
        idris2 $IDRIS_ARGS "$file" || fail "$file"
    fi
done

if [ $_fail = 1 ] ; then
    echo
    echo "ERROR: Some tests failed"
    exit 1
fi

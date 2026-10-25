#!/bin/bash
# the whole-orbit search, three role assignments of Table 1's scheme, 240 starts each
cd "$(dirname "$0")" || exit 1
echo "# gamma_{inf,2} whole-orbit search $(date '+%Y-%m-%d %H:%M')"
for role in 0 1 2; do python3 search_gl.py table1 $role 240 $((10000 * (role + 1))); done
echo "# done $(date '+%H:%M')"

#!/bin/zsh
# Stored as run on 2026-11-10 from the session scratch directory (kres/deep/p67.zsh): the scratch paths are kept;
# kres_census is src/bin/kres.rs as committed with this file, kres_fast4 is commit 8df5b76's build.
# chain: the k = 11 sweep (p6), then the depth-2 pass over its open lines (p7); p7 only if p6 ends clean
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
/bin/zsh "$S/kres/deep/p6.zsh" && /bin/zsh "$S/kres/deep/p7.zsh"
echo "=== chain ended $(date '+%H:%M:%S')" >> "$S/kres/deep/p6.log"

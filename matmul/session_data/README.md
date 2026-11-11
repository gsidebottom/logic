# Session scratch mirrors

Each folder here is a copy of one Claude Code session's scratch directory (its "scratchpad"),
taken because that directory is deleted when the session ends.  The folders are gitignored:
they hold several GB, mostly regenerable intermediates, and exist only on Greg's machine.
Committed notes, drivers and logs that say "scratchpad X", "$S/X" or "the session scratch
directory ... X" mean `matmul/session_data/<folder>/X`.

| folder | session | copied | size |
|---|---|---|---|
| 2026-11_fde6fc44 | fde6fc44-1302-4fb7-9f35-47e08b29f1c6 | 2026-11-11 07:02 with `rsync -a`, refreshed with the same command | 5.8 GB |

The copy leaves out `kres/target_census/` (a cargo target directory).  What the committed
material points to in 2026-11_fde6fc44:

- `kres/`: the k-subset re-solve (src/bin/kres.rs).  `deep/` holds the k = 8..11 sweeps
  (drivers p3..p9, logs, and the per-class line files, e.g. `P6_<class>_k11.txt`, 158-300 MB
  each); `build/` holds the binaries the drivers name (`kres_census`, `kres_fast4`);
  `exact/`, `ctrl/`, `reg/`, `gate/` hold the earlier passes, controls and regressions.
- `wp/reps/<class>.bits`: the rank-47 class representatives the kres drivers read.  They are
  byte-identical to committed files: km47 = matmul/seeds4/km47-0.bits, at47 =
  matmul/seeds4/alphatensor47.bits, ref47 = matmul/x47/walkseeds/ref47.bits, proj47_5 =
  matmul/tomar_line/proj/found47/r47-00005.bits, projkm47_7 =
  matmul/tomar_line/proj/found47_km56/d180/r47-00007.bits.
- `kronscan/`: the 2-reducibility scans and the projection records.  `proj/red/` and
  `proj/red2/` hold the exact intermediate projections, `multi/` the deletion experiments,
  `cat/` the catalog sweep, `stored/` unzipped copies of the stored records.  The records
  themselves, their pivot paths and logs are committed in matmul/tomar_line/proj/kron_reduced/,
  kron_runs/ and logs/.
- `plinopt_x166/`: the PLinOpt worktree of PR jgdumas/plinopt#39 (merged 2026-11-10).
- The other folders (pspace, mb2, walk_all*, km445_*, own445*, hpool_d8*, lexlong, lexpilot,
  move*, ...) are earlier work of the same session; the READMEs that cite them say what they are.

Some folders contain downloaded third-party material (papers, published schemes).  Keep it
here; nothing in these mirrors is to be committed or redistributed.

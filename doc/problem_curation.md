
```zsh
tools/gbd/download.sh "minisat1m=yes and variables<1500 and clauses<15000 and (family=agile or family=pigeon-hole or family=coloring or family=tseitin-formulas or family=scheduling or family=hamiltonian or family=hardware-verification or family=cryptography or family=prime-factoring)"
```

cur
```zsh
tools/gbd/curate.py \
    --query "variables<2000 and (result=sat or result=unsat)" \
    --timeout 60 --parallel 8 --max-instances 200 \
    --verify-unsat --verify-timeout 30 --refresh \
    --index $BENCH_DIR/evo_fitness.jsonl
```

```zsh
rm /Users/greg/projects/logic/doc/sweeps/evo_fitness_eff_60s/sweep_eff_tau_*.{md,png}
tools/gbd/sweep_eff_tau.py \
    --index /Users/greg/projects/curated_benchmarks/evo_fitness.jsonl \
    --filter "r['status']=='SAT' or r['status']=='UNSAT'" \
    --backend eff --timeout 60 -j 10
```
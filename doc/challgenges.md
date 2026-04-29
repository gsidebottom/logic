# Challenging SAT Problems

## Adder Diagnosis
### n bit adder 1+1=3 with at most 1 fault

3 bit adder takes 1s
```jq
faulty_add_at_most(3;1;1;0;3;0;1)
```

4 bit adder takes 2m26s with no cover
```jq
faulty_add_at_most(4;1;1;0;3;0;1)
```

## hwmcc20
in `/Users/greg/projects/aiger`
```zsh
export k=20
./aigmove hwmcc20/aig/2020/mann/rast-p11.aig moved.aig
./aigunroll "$k" moved.aig > unrolled.aig
./aigtocnf unrolled.aig > rast-p11.k"$k".cnf
head rast-p11.k"$k".cnf
```

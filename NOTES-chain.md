# c10-chain working notes (session scratch; not a design doc)
- Task: port simC10 entries 9 (CHAIN, try_chain3W) and 23 (ABSORB, try_absorb3) into bb/l3c10-chain.sl.
- Rocq dump of all CHAIN/ABSORB instances to move 40035: /tmp/claude-0/rocqsim/K (k_<m>_in/out.txt, list.txt),
  driver /tmp/claude-0/rocqsim/ocK/drvK.ml (system ocamlfind, not opam).
- f7fbe185: mac-chain / mac-absorb in bb/l3c10-chain.sl; test driver kmain in bb/l3c10-chain-t.sl
  (input: idx, Rocq in-config, Rocq out-config; prints MATCH/DIFF/NOFIRE). Batch: /tmp/claude-0/rocqsim/KR/run.sh.
- v1 batch (res1): all 42 ABSORB MATCH; 39956 ABSORB 213 s vs Rocq 481 s; 38507 CHAIN 17 s vs 127 s.
- Per marker cost: phi-run(s-k) + rd-run (maximality) + ident (phi-run + compare) + cells: O(P) each.

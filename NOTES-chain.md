# c10-chain working notes (session scratch; not a design doc)
- Task: port simC10 entries 9 (CHAIN, try_chain3W) and 23 (ABSORB, try_absorb3) into bb/l3c10-chain.sl.
- Rocq dump of all CHAIN/ABSORB instances to move 40035: /tmp/claude-0/rocqsim/K (k_<m>_in/out.txt, list.txt),
  driver /tmp/claude-0/rocqsim/ocK/drvK.ml (system ocamlfind, not opam).
- f7fbe185: mac-chain / mac-absorb in bb/l3c10-chain.sl; test driver kmain in bb/l3c10-chain-t.sl
  (input: idx, Rocq in-config, Rocq out-config; prints MATCH/DIFF/NOFIRE). Batch: /tmp/claude-0/rocqsim/KR/run.sh.
- v1 batch (res1): all 42 ABSORB MATCH; 39956 ABSORB 213 s vs Rocq 481 s; 38507 CHAIN 17 s vs 127 s.
- Per marker cost: phi-run(s-k) + rd-run (maximality) + ident (phi-run + compare) + cells: O(P) each.
- In-situ harness: bb/l3c10drv.ml hints mode emits "3 idx ..." records for macro indices in env C10CHK (e.g. 9,23);
  bb/l3c10h.sl hloop kind 3 runs c10-mac (bb/l3c10-chain.sl) and requires the result equal Rocq's (HBad 6 = no fire,
  7 = differs). Load order: ... bb/l3c10.sl bb/l3c10-chain.sl bb/l3c10h.sl main.sl.
  Hint streams: /tmp/claude-0/rocqsim/H/h1.txt (0-22268), h2.txt (22268-40035); driver build /tmp/claude-0/rocqsim/ocH.
- Results (7792caa5): 76/76 dump instances MATCH (34 CHAIN, 42 ABSORB); in-situ hint streams 1-22268 and
  22269-40035 OK with end configs equal to Rocq's. Big moves, OCAMLRUNPARAM=s=32M, single runs, input parse included
  (39956's parse alone is ~16 s): 22262 2.1 s (Rocq 15 s), 38259 5.9 s (11 s), 38507 14.7 s (121-127 s),
  39019 8.2 s (21 s), 39739 7.3 s (23 s), 39956 84 s (403-481 s).
- Next for speed: each marker still costs two phi computations (jump target and identification) plus sweeps;
  lin3s8's snoc/decrement laws would remove them but are not ported.

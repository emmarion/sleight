#!/usr/bin/env python3
"""Times slc on generated programs of doubling size, one shape each, and prints each time with its ratio to
the previous size's: a ratio near 2 is linear, near 4 quadratic. Usage: bench/scale.py slc [shape ...]"""
import os, subprocess, sys, tempfile, time
def wide_scope(n):
    out=["(def-lvl L)"]
    for i in range(n): out.append(f"(def-fns L $ (many g{i} : (many (Nat) n) -> (many (Nat) r))\n  (nat-add n {i}))")
    out.append("(g0 1)"); return out
def long_body(n):
    out=["(def-fns _ $ (many body : (many (Nat) n) -> (many (Nat) r))"]
    for i in range(n): out.append(f"  (let ((many v{i})) (nat-add n {i%7}))")
    out.append(f"  v{n-1})\n(body 3)"); return out
def body_meta(n):
    out=["(def-fns _ $ (many step : (erased Type A) (many (List A) xs) (many A x) -> (many (List A) r))\n  (Cons _ x xs))",
         "(def-fns _ $ (many body : (many (Nat) n) -> (many (List $ Nat) r))","  (let ((many xs0)) (Nil (Nat)))"]
    for i in range(n): out.append(f"  (let ((many xs{i+1})) (step _ xs{i} n))")
    out.append(f"  xs{n})\n(body 3)"); return out
def many_adts(n):
    out=[]
    for i in range(n):
        out.append(f"(def-adts $ (T{i} : -> Type)\n  enum\n  (many TA{i} : -> (T{i}))\n  (many TB{i} : (many (Nat) n) -> (T{i})))")
        out.append(f"(def-fns _ $ (many f{i} : (many (T{i}) x) -> (many (Nat) r))\n  (match many x _ ((TA{i}) 0) ((TB{i} n) n)))")
    out.append("(f0 (TA0))"); return out
def wide_enum(n):
    out=["(def-adts $ (W : -> Type)\n  enum\n"+"\n".join(f"  (many W{i} : -> (W))" for i in range(n))+")",
         "(def-fns _ $ (many f : (many (W) w) -> (many (Nat) r))\n  (match many w _ "+" ".join(f"((W{i}) {i%5})" for i in range(n))+"))","(f (W0))"]
    return out
def deep_expr(n):
    return ["(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))\n  "+"(nat-add 1 $ "+"nat-add 1 $ "*(n-2)+"nat-add 1 n))","(f 1)"]
def nested_match(n):
    body="0"
    for i in reversed(range(n)):
        v="n" if i==0 else f"m{i-1}"
        body=f"(match many {v} _ ((Zero) 0) ((Succ m{i}) {body}))"
    return [f"(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))\n  {body})","(f 1)"]
def long_string(n):
    return ['(let ((many s)) "'+("ab"*(n//2))+'")', "s"]
def many_lits(n):
    return ["(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))\n  "+"(nat-add "*0+" ".join([])+"n)"]+[f"(let ((many c{i})) {i*1000+7})" for i in range(n)]+["c0"]
def many_params(n):
    ps=" ".join(f"(many (Nat) a{i})" for i in range(n))
    return [f"(def-fns _ $ (many f : {ps} -> (many (Nat) r))\n  a0)", "(f "+" ".join("1" for _ in range(n))+")"]
def big_block(n):
    fs=[]
    for i in range(n):
        nxt=(i+1)%n
        fs.append(f"  ((many h{i} : (subterm many (Nat) n) -> (many (Nat) r))\n    (match many n _ ((Zero) 0) ((Succ m) (h{nxt} m))))")
    return ["(def-fns _\n"+"\n".join(fs)+")","(h0 5)"]
def comptime_list(n):
    return ["(let ((many xs)) "+"(Cons (Nat) 1 $ "*n+"Nil (Nat))", "(length _ xs)"] if False else ["(let ((many xs)) "+"(Cons (Nat) 1 $ "+"Cons (Nat) 1 $ "*(n-1)+"Nil (Nat)))","xs"]
def wild_list(n):
    return ["(let ((many xs)) "+"(Cons _ 1 $ "+"Cons _ 1 $ "*(n-1)+"Nil (Nat)))","xs"]
def body_list(n):
    return ["(def-fns _ $ (many f : (many (Nat) n) -> (many (List $ Nat) r))\n  "+"(Cons (Nat) n $ "+"Cons (Nat) n $ "*(n-1)+"Nil (Nat)))","(f 1)"]
def nested_ctor(n):
    return ["(def-adts $ (U : -> Type)\n  enum\n  (many UZ : -> (U))\n  (many US : (many (U) t) -> (U)))","(let ((many u)) "+"(US $ "+"US $ "*(n-1)+"UZ))","u"]
def many_uniques(n):
    out=["(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))"]
    for i in range(n): out.append(f"  (let ((unique u{i})) (Zero))\n  (let ((many w{i})) (share u{i}))")
    out.append("  n)\n(f 1)"); return out
def many_branches_body(n):
    # sequence of n small matches in one body
    out=["(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))"]
    for i in range(n): out.append(f"  (let ((many v{i})) (match many n (((Nat) r)) ((Zero) 0) ((Succ m) m)))")
    out.append("  n)\n(f 1)"); return out
def many_toplevel_lets(n):
    return [f"(let ((many x{i})) (nat-add 1 {i}))" for i in range(n)]+["x0"]
def long_lines(n):
    return ["; "+"x"*n, "1"]
def comptime_gen(n):
    return ["(def-fns _ $ (many gen : (subterm many (Nat) n) (many (List $ Nat) acc) -> (many (List $ Nat) r))\n  (match many n _ ((Zero) acc) ((Succ j) (tail $ gen j (Cons (Nat) j acc)))))",
            f"(let ((many big)) (gen {n} (Nil (Nat))))","big"]
def comptime_fold(n):
    return ["(def-fns _ $ (many gen : (subterm many (Nat) n) (many (Nat) acc) -> (many (Nat) r))\n  (match many n _ ((Zero) acc) ((Succ j) (tail $ gen j (nat-add acc 1)))))",
            f"(let ((many t)) (gen {n} 0))","t"]
def many_letmatch(n):
    out=["(def-fns _ $ (many f : (many (List $ Nat) xs) -> (many (Nat) r))"]
    for i in range(n): out.append(f"  (let-match many {'xs' if i==0 else 'r'+str(i-1)} (Cons _ h{i} r{i}) ((Nil _) 0))")
    out.append("  h0)\n(f (Nil (Nat)))"); return out
def nested_defs(n):
    s="n"
    for i in range(n): s=f"(def-fns _ $ (many d{i} : (many (Nat) n) -> (many (Nat) r))\n {s})\n n"
    return ["(def-fns _ $ (many top : (many (Nat) n) -> (many (Nat) r))\n "+s+")","(top 1)"]
def wide_values(n):
    rets=" ".join(f"(many (Nat) r{i})" for i in range(n))
    vals=" ".join("n" for i in range(n))
    binds=" ".join(f"(many v{i})" for i in range(n))
    return [f"(def-fns _ $ (many f : (many (Nat) n) -> {rets})\n  (values {vals}))", f"(let ({binds}) (f 1))","v0"]
def wide_enum_else(n):
    out=["(def-adts $ (W : -> Type)\n  enum\n"+"\n".join(f"  (many W{i} : -> (W))" for i in range(n))+")"]
    out.append("(def-fns _ $ (many f : (many (W) w) -> (many (Nat) r))\n  (match many w _ ((W0) 1) (else 0)))")
    out.append(f"(f (W{n-1}))"); return out
def many_errors(n):
    return [f"(let ((many (Nat) x{i})) \"s\")" for i in range(n)]
def many_calls_body(n):
    out=["(def-fns _ $ (many g : (many (Nat) a) (many (Nat) b) -> (many (Nat) r))\n  (nat-add a b))","(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))","  (let ((many v0)) n)"]
    for i in range(n): out.append(f"  (let ((many v{i+1})) (g v{i} n))")
    out.append(f"  v{n})\n(f 1)"); return out

SHAPES = {k: v for k, v in list(globals().items()) if callable(v) and v.__module__ == '__main__' and k != 'main'}
SIZES = {'long_string': [20000, 40000, 80000], 'comptime_gen': [10000, 20000, 40000], 'comptime_fold': [10000, 20000, 40000]}

def main():
    slc, names = sys.argv[1], sys.argv[2:] or sorted(SHAPES)
    with tempfile.TemporaryDirectory() as d:
        for name in names:
            prev = None
            for n in SIZES.get(name, [400, 800, 1600]):
                path = os.path.join(d, f"{name}.sl")
                with open(path, 'w') as f:
                    f.write("\n".join(SHAPES[name](n)) + "\n")
                t = time.time()
                subprocess.run([slc, path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                t = time.time() - t
                print(f"{name:20} {n:6} {t:7.2f}s" + (f"  x{t / prev:.1f}" if prev else ""), flush=True)
                prev = t

main()

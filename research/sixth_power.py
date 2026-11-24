"""Generate exact-component certificates for the sixth-power-free least-prime sieve."""

import argparse
from collections import Counter
from functools import cache
from math import gcd
from pathlib import Path

from count_chain import Factorer, TRIAL_PRIMES, probable_prime

factorer = Factorer(0.20)
test = "(by decide +kernel)"


@cache
def local_factors(p, e):
    """Propose factors. All divisibility tests and primality proofs are replayed in Lean."""
    n = (p**(e+1)-1)//(p-1)
    if n.bit_length() <= 100:
        return tuple(factorer.partial(n)[0])
    factors = []
    for q in TRIAL_PRIMES:
        while n % q == 0:
            factors.append(q)
            n //= q
    if n > 1 and n.bit_length() < 160 and probable_prime(n):
        factors.append(n)
    return tuple(factors)


class Sieve:
    def __init__(self, root):
        self.root = root
        self.rows = []
        self.primes = set()
        self.stats = Counter()

    def prime(self, p):
        if p < 32:
            return "(by norm_num)"
        self.primes.add(p)
        return f"sixPrime{self.root}_{p}"

    def extend(self, path, need, D, S, p):
        states = []
        for e in range(1, 6):
            next_need = need.copy()
            next_need.update(q for q in local_factors(p, e) if q > 2)
            states.append(self.visit(path | {p: e}, next_need, D*p**e, S*((p**(e+1)-1)//(p-1))))
        return states

    def visit(self, path, need, D, S):
        forced = S//gcd(S, 2*D)
        if S % 4 == 0 or S > 2*D or gcd(D, forced) != 1:
            self.stats['automatic'] += 1
            return f"closed_impossible {test}"
        for p, n in sorted(need.items()):
            if p < self.root and forced % p == 0:
                self.stats['smaller'] += 1
                return f"closed_smaller (q:={p}) (by decide) (by decide) {test}"
            if n >= 6 and forced % p**6 == 0:
                self.stats['sixth'] += 1
                return f"closed_sixth (q:={p}) {self.prime(p)} {test}"
        def score(p):
            # Favor branches that immediately lose several allowable exponents.
            allowed = [e for e in (1,2,4,5) if e>=need[p] and
                       (e%2==0 or (all(b%2==0 for b in path.values()) and p%4==1))]
            def survives(e):
                fs = Counter(local_factors(p,e))
                return all(q==2 or (q>=self.root and need[q]+v<=path.get(q,5)) for q,v in fs.items())
            return sum(survives(e) for e in allowed), p
        available = sorted(p for p in need if p not in path and forced % p == 0)
        if not available:
            raise RuntimeError(f"No forced prime found at {path}")
        p = min(available[:10], key=score)
        if len(path)>80 or p.bit_length()>200:
            raise RuntimeError(f"Factor search exceeded its discovery limit at {path}")
        children = self.extend(path,need,D,S,p)
        name = f"sixCase{self.root}_{len(self.rows)}"
        node = f"⟨{D},{S},{sum(path.values())},{len(path)}⟩"
        lines = [f"theorem {name} : Closed {self.root} {node} := by",
                 f"  apply closed_split (p:={p}) {self.prime(p)} {test}",
                 "  intro j", "  fin_cases j", *["  · exact "+x for x in children], ""]
        self.rows.append(lines)
        return name

    def write(self, out, chunk):
        k = self.root
        children = self.extend({},Counter(),1,1,k)
        self.rows.append([f"theorem no_sixth_free_min_{k} {{N : ℕ}} (H : Hyp N {k}) (hd : {k}∣N) : False := by",
                          f"  apply root_split H {self.prime(k)} hd", "  intro j", "  fin_cases j",
                          *["  · exact "+x for x in children], ""])
        out.mkdir(parents=True, exist_ok=True)
        ns = f"OddPerfect.SixthLeast{k}"
        previous = "OddPerfect.SixthPowerChain"
        def emit(name, rows):
            nonlocal previous
            lines = ["module", "", f"public import {previous}", "import Mathlib.Tactic.Primality",
                     "import Mathlib.Tactic.FinCases", "", "public section", "",
                     "namespace OddPerfect.SixthPowerChain", "", "set_option maxRecDepth 16000", "",
                     *rows, "end OddPerfect.SixthPowerChain", ""]
            (out/f"{name}.lean").write_text("\n".join(lines))
            previous = ns+"."+name
        witness = []
        for p in sorted(self.primes):
            witness.extend([f"theorem sixPrime{k}_{p} : Nat.Prime {p} :=", "  "+factorer.prime_proof(p), ""])
        if witness:
            emit("Primes", witness)
        for i in range(0, len(self.rows), chunk):
            emit(f"Part{1+i//chunk:03d}", [line for row in self.rows[i:i+chunk] for line in row])
        print(k,len(self.rows),"splits",dict(self.stats),len(self.primes),"prime witnesses",previous,flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prime", type=int)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--chunk", type=int, default=16)
    args = parser.parse_args()
    Sieve(args.prime).write(args.output,args.chunk)

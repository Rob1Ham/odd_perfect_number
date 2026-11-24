"""Emit exact covers for odd harmonic integers violating a divisor-count bound."""

import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from pathlib import Path

from divisor_count import envelope, prime, rat


@cache
def prime_divisors(n):
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        result.append(n)
    return result


@dataclass
class Branch:
    name: str
    state: tuple
    q: int
    children: list
    cutoff: int


def generate(d):
    branches = []
    bounds = set()

    def bound(p):
        bounds.add(p)
        return f"envH{d}_{p}"

    def visit(D, T, S, p):
        weight = Fraction(T**d, D)
        E = envelope(p, d, 1)
        if weight * E <= 1:
            return f"closed_by_moment {bound(p)} (by decide +kernel)"
        if D < T**d and D*T % S == 0:
            raise ValueError(f"unexcluded harmonic prefix {D}")
        if p >= 2**d:
            if weight * Fraction(2**d, p) <= 1:
                return "closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)"
            for r in prime_divisors(S):
                if D*T % r == 0:
                    continue
                v = min(r-1, 12)
                cost = Fraction((v+1)**d, p**v)
                if r >= p:
                    e = 1 if r % 4 == 1 else 2
                    cost = max(cost, Fraction((e+1)**d, r**e))
                if weight * cost <= 1:
                    prime_proof = "by norm_num" if r >= 500 else "by decide +kernel"
                    return (f"closed_owed_prime (r:={r}) (v:={v}) (by decide) (by decide) "
                            f"({prime_proof}) (by decide +kernel) (by decide +kernel) (by decide) "
                            "(by decide +kernel) (by decide +kernel)")
        q = p+1
        while not prime(q):
            q += 1
        children = []
        for e in range(120):
            local = Fraction((e+1)**d, p**e)
            if e >= 8 and weight * local * envelope(q, d, 1) <= 1:
                bound(q)
                name = f"harmonic{d}_{len(branches)}"
                branches.append(Branch(name, (D,T,S,p), q, children, e))
                return name
            if pow(p, e, 4) != 1:
                children.append(None)
            else:
                g = (p**(e+1)-1)//(p-1)
                children.append("exact "+visit(D*p**e, T*(e+1), S*g, q))
        raise ValueError("uncovered exponent tail")

    root = visit(1,1,1,3)
    return branches,bounds,root


def write_project(directory, d, chunk):
    branches,bounds,root = generate(d)
    directory.mkdir(parents=True,exist_ok=True)
    ns = f"OddPerfect.HarmonicCount{d}"
    def write(name,dep,lines):
        imports = [] if name == "Envelopes" else ["import Mathlib.Tactic.IntervalCases"]
        if any("by norm_num" in line for line in lines):
            imports.append("import Mathlib.Tactic.NormNum.Prime")
        (directory/f"{name}.lean").write_text("\n".join(["module", "", f"public import {dep}", *imports, "",
            "public section", "", "namespace OddPerfect.HarmonicSearch", "", "open DivisorCountSearch", "",
            *lines, "end OddPerfect.HarmonicSearch", ""]))

    env = []
    for p in sorted(bounds):
        env.extend([f"theorem envH{d}_{p} : ResidualBound {p} {d} 1 {rat(envelope(p,d,1))} :=",
                    f"  residual_envelope (C:={2**d}) (by decide) (by decide +kernel) "
                    "(by decide +kernel) (by decide +kernel)", ""])
    write("Envelopes","OddPerfect.HarmonicSearch",env)
    previous=ns+".Envelopes"
    for offset in range(0,len(branches),chunk):
        lines=[]
        for node in branches[offset:offset+chunk]:
            D,T,S,p=node.state
            lines.extend([f"theorem {node.name} : Closed {d} {D} {T} {S} {p} := by",
                          f"  apply closed_split (a:={node.q}) (by decide) (by decide +kernel)",
                          "  intro e hres", f"  by_cases h : e < {node.cutoff}", "  · interval_cases e"])
            for e,child in enumerate(node.children):
                if child is None:
                    child=f"exact ((by decide : ¬ ({p}:ℕ)^{e}%4=1) hres).elim"
                lines.append("    · "+child)
            lines.extend([f"  · apply closed_of_plain",
                          f"    exact close_exponent_tail (H:={node.cutoff}) (by decide) (by decide) (by decide) "
                          f"(by decide +kernel) (by decide) envH{d}_{node.q} (by decide +kernel) e (by omega)", ""])
        name=f"Part{1+offset//chunk:02d}"
        write(name,previous,lines)
        previous=ns+"."+name
    print(d, "splits",len(branches),"envelopes",len(bounds),"root",root,"import",previous)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree",type=int,choices=(3,4))
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--chunk",type=int,default=20)
    args=parser.parse_args()
    write_project(args.output,args.degree,args.chunk)

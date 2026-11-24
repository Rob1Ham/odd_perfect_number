"""Generate certificates for Cohen and Sorli's odd divisor-count bounds."""

import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from math import isqrt
from pathlib import Path


@cache
def prime(p):
    return p >= 2 and all(p % q for q in range(2, isqrt(p) + 1))


@cache
def cutoff(k, s):
    c = 1
    while c**s < 2**k:
        c += 1
    return c


@cache
def envelope(a, k, s):
    result = Fraction(1)
    for p in range(a, cutoff(k, s)):
        if prime(p):
            if 10**k > p**s * 9**k:
                raise ValueError("invalid peak exponent cap")
            result *= max(Fraction((e + 1)**k, p**(s * e)) for e in range(9))
    return result


@dataclass(frozen=True)
class Leaf:
    k: int
    s: int
    kind: str


@dataclass
class Branch:
    n: int
    D: int
    T: int
    p: int
    q: int
    children: list
    tail: Leaf


def generate(d, B):
    slopes = [(d,1), (d+1,1), (2*d+1,2), (3*d+1,3), (4*d+1,4), (5*d+1,5),
              (3*d+2,3), (5*d+2,5), (7*d+3,7), (7*d+10,7), (d+2,1), (d+3,1)]
    states = []
    bounds = set()

    def visit(D, T, p):
        if D >= B and T**d > D:
            raise ValueError(f"counterexample {D}, divisor count {T}")
        lower = max(B, D)
        for k, s in slopes:
            prefix = Fraction(T**k, D**s)
            limit = lower**(k - d*s)
            if (prefix * envelope(p,k,s))**d <= limit:
                bounds.add((p,k,s))
                return Leaf(k,s,"envelope")
            if p**s >= 2**k and (prefix * Fraction(2**k,p**s))**d <= limit:
                return Leaf(k,s,"nonempty")
        q = p+1
        while not prime(q):
            q += 1
        children = []
        for e in range(10000):
            if e >= 8:
                for k, s in slopes:
                    if 10**k > p**s * 9**k:
                        continue
                    upper = Fraction((T*(e+1))**k, (D*p**e)**s) * envelope(q,k,s)
                    if upper**d <= max(B,D*p**e)**(k-d*s):
                        bounds.add((q,k,s))
                        node = Branch(len(states),D,T,p,q,children,Leaf(k,s,"tail"))
                        states.append(node)
                        return node
            children.append(visit(D*p**e,T*(e+1),q))
        raise ValueError("exponent tail did not close")

    root = visit(1,1,3)
    return states,bounds,root


def rat(w):
    return f"({w.numerator}/{w.denominator} : ℚ)"


def env_name(d, a, k, s):
    return f"bound{d}_{a}_{k}_{s}"


def leaf_expr(d, p, obj):
    if isinstance(obj, Branch):
        return f"node{d}_{obj.n}"
    k,s=obj.k,obj.s
    if obj.kind == "envelope":
        return f"close_envelope (by decide) (by decide) {env_name(d,p,k,s)} (by decide +kernel)"
    return (f"close_nonempty (k:={k}) (s:={s}) (by decide) (by decide) (by decide) "
            "(by decide) (by decide +kernel) (by decide +kernel)")


def write_project(directory, d, B, parents_per_module=20):
    states, bounds, root = generate(d,B)
    directory.mkdir(parents=True,exist_ok=True)
    base = f"OddPerfect.DivisorCount{d}"
    def write(name, dep, entries):
        tactics = [] if name == "Envelopes" else ["import Mathlib.Tactic.IntervalCases"]
        (directory/f"{name}.lean").write_text("\n".join([
            "module", "", f"public import {dep}", *tactics, "", "public section", "",
            "namespace OddPerfect.DivisorCountSearch", "", *entries, "end OddPerfect.DivisorCountSearch", ""]))
    lines=[]
    for a,k,s in sorted(bounds):
        lines += [f"theorem {env_name(d,a,k,s)} : ResidualBound {a} {k} {s} {rat(envelope(a,k,s))} :=",
                  f"  residual_envelope (C:={cutoff(k,s)}) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)", ""]
    write("Envelopes","OddPerfect.DivisorCountBounds",lines)
    prev=f"{base}.Envelopes"
    for offset in range(0,len(states),parents_per_module):
        lines=[]
        for b in states[offset:offset+parents_per_module]:
            H=len(b.children)
            lines += [f"theorem node{d}_{b.n} : Closed {d} {B} {b.D} {b.T} {b.p} := by",
                      f"  apply closed_of_split (a:={b.q}) (by decide) (by decide +kernel)",
                      "  intro e",f"  by_cases h : e<{H}","  · interval_cases e"]
            for child in b.children:
                lines.append("    · exact "+leaf_expr(d,b.q,child))
            k,s=b.tail.k,b.tail.s
            lines.extend([f"  · exact close_exponent_tail (H:={H}) (by decide) (by decide) (by decide) (by decide +kernel)",
                          f"      (by decide) {env_name(d,b.q,k,s)} (by decide +kernel) e (by omega)", ""])
        part=f"Part{1+offset//parents_per_module:02d}"
        write(part,prev,lines);prev=base+"."+part
    print(d,B,len(states),"split nodes,",len(bounds),"envelopes; final",prev,leaf_expr(d,3,root),flush=True)


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree",type=int,choices=(2,3,4,5))
    parser.add_argument("threshold",type=int,help="inclusive lower endpoint")
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    write_project(args.output,args.degree,args.threshold)

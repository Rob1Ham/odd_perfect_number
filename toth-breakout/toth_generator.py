"""Generate Lean covers for the odd-multiplier case of Tóth's cofactor set."""

import argparse
from dataclasses import dataclass
from functools import cache
from pathlib import Path

from divisor_count import prime


@cache
def next_prime(p):
    q = p + 2
    while not prime(q):
        q += 2
    return q


@dataclass
class Branch:
    D: int
    S: int
    p: int
    q: int
    children: list
    name: str


def next_multiplier(D, S):
    z = max(5, S // (2*D*D-S) + 1)
    return z + (1-z) % 4


def point(root, S):
    gap = 2*root*root - S
    if gap <= 0:
        return
    x, remainder = divmod(S,gap)
    if remainder == 0 and x >= 5 and x % 4 == 1 and (root,x) != (3003,22021):
        raise ValueError(f"unexpected feasible point: {root}, {x}")


def generate(B):
    branches = []
    def visit(D, S, p):
        point(D,S)
        if S >= 2*D*D:
            return "closed_abundant (by decide +kernel) (by decide +kernel)"
        if D*p > B:
            return "closed_root_only (by decide +kernel) (by decide +kernel)"
        t = next_multiplier(D,S)
        k = 0
        product = D
        while product*p <= B:
            product *= p
            k += 1
        if S*p**k*(t+1) <= 2*t*D*D*(p-1)**k:
            return (f"closed_interval (k:={k}) (by decide) (by decide +kernel) "
                    "(by decide +kernel) (by decide +kernel)")
        if D*p*p > B:
            for r in range(p, B//D+1):
                point(D*r,S*(r*r+r+1))
            width = B//D+1-p
            if width > 2048:
                depth = ((width-1)//32).bit_length()
                return f"closed_last_prime_range {depth} (by decide +kernel) (by decide +kernel) (by decide +kernel)"
            return "closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)"
        q = next_prime(p)
        E = G = 1
        children = []
        while D*E <= B:
            children.append(visit(D*E,S*G,q))
            E *= p
            G = G*p*p + p + 1
        name = f"case{len(branches)}"
        branches.append(Branch(D,S,p,q,children,name))
        return name
    root = visit(1,1,3)
    return branches,root


def write_project(directory, B, chunk):
    nodes, root = generate(B)
    directory.mkdir(parents=True,exist_ok=True)
    previous = "OddPerfect.TothCover"
    for offset in range(0,len(nodes),chunk):
        imports = [f"public import {previous}", "import Mathlib.Tactic.IntervalCases"]
        if any("closed_last_prime_range" in child for b in nodes[offset:offset+chunk] for child in b.children):
            imports.append("import OddPerfect.TothIntervals")
        imports.append("import Mathlib.Tactic.NormNum.Prime")
        lines=["module", "", *imports, "",
               "public section", "", "namespace OddPerfect.Toth", ""]
        for branch in nodes[offset:offset+chunk]:
            limit=len(branch.children)
            lines.extend([f"theorem {branch.name} : Closed {B} {branch.D} {branch.S} {branch.p} := by",
                          f"  apply closed_split (a:={branch.q}) (by norm_num) (by decide +kernel)", "  intro e he",
                          f"  have ht : e < {limit} := by",
                          f"    by_contra! h", f"    have := Nat.mul_le_mul_left {branch.D} "
                          f"(Nat.pow_le_pow_right (by decide : 0<{branch.p}) h)",
                          f"    have hnum : {B} < {branch.D}*{branch.p}^{limit} := by decide +kernel", "    omega",
                          "  interval_cases e"])
            lines.extend(f"  · exact {child}" for child in branch.children)
            lines.append("")
        lines.extend(["end OddPerfect.Toth",""])
        part=f"Part{1+offset//chunk:02d}"
        (directory/f"{part}.lean").write_text("\n".join(lines))
        previous=f"OddPerfect.TothTrillion.{part}"
    print("split nodes",len(nodes),"root",root,"final import",previous)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-limit",type=int,default=10**6)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--chunk",type=int,default=20)
    args=parser.parse_args()
    write_project(args.output,args.root_limit,args.chunk)
